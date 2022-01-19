open System
open System.Security.Cryptography
open System.Text
open System.Text.RegularExpressions
open System.IO
open System
open System.Threading
open Akka.Actor
open Akka.Actor
open Akka.Configuration
open Akka.FSharp
open FSharp.Data
open FSharp.Data.HttpRequestHeaders
type Bundle_akka_P = Bundle8 of  string*string * string* string* string * string* string* string * string

let N = 2
let M = N

type AesEncryption(?mode:string, ?size:int) = 
    let modes = Map.empty.Add("CBC", CipherMode.CBC).Add("CFB", CipherMode.CFB)
    let Sizes  = [ 128; 192; 256 ]
    let lengthOfSalt = 16
    let lengthOfIV = 16
    let lengthOfMAC = 32
    let lengthOfMACKey = 32

    let mode = (defaultArg mode "CBC").ToUpper()
    let lengthOfKey = (defaultArg size 128) / 8
    let size = defaultArg size 128
    let mutable masterKey:byte[] = null

    do
        if not (List.exists ((=) size) Sizes ) then
            raise (ArgumentException "Invalid key size!")
        if not (modes.ContainsKey mode) then
            raise (ArgumentException (mode + " is not supported!"))

    member val keyIterations = 20000 with get, set
    member val base64 = true with get, set

    member this.Encrypt(data:byte[], ?pwd:string):byte[] = 
        let iv = this.RandomBytes lengthOfIV
        let salt = this.RandomBytes lengthOfSalt
        try
            let AESkey, macKey = this.Keys(salt, (defaultArg pwd null))

            use cipher = this.Cipher(AESkey, iv)
            use ict = cipher.CreateEncryptor()
            let ciphertext = ict.TransformFinalBlock(data, 0, data.Length)

            let iv_ct = Array.append iv ciphertext
            let mac = this.Sign(iv_ct, macKey)
            let encrypt = Array.append (Array.append salt iv_ct) mac

            if this.base64 then
                Encoding.ASCII.GetBytes (Convert.ToBase64String encrypt)
            else
                encrypt
        with 
            | :? ArgumentException as e -> this.ErrorHandler e; null
            | :? CryptographicException as e -> this.ErrorHandler e; null
    
    member this.Encrypt(data:string, ?pwd:string):byte[] = 
        this.Encrypt (Encoding.UTF8.GetBytes(data), (defaultArg pwd null))
    
    member this.Decrypt(data:byte[], ?pwd:string):byte[] = 
        let mutable data = data
        try
            if this.base64 then 
                data <- Convert.FromBase64String(Encoding.ASCII.GetString data)
            
            let salt = data.[0..lengthOfSalt - 1]
            let iv = data.[lengthOfSalt..lengthOfSalt + lengthOfIV - 1]
            let ciphertext = data.[lengthOfSalt + lengthOfIV..data.Length - lengthOfMAC - 1]
            let mac = data.[data.Length - lengthOfMAC..data.Length - 1]

            let AESkey, macKey = this.Keys(salt, (defaultArg pwd null))
            this.Verify((Array.append iv ciphertext), mac, macKey)

            use cipher = this.Cipher(AESkey, iv)
            use ict = cipher.CreateDecryptor()
            let plaintext = ict.TransformFinalBlock(ciphertext, 0, ciphertext.Length)
            plaintext
        with 
            | :? ArgumentException as e -> this.ErrorHandler e; null
            | :? CryptographicException as e -> this.ErrorHandler e; null
            | :? FormatException as e -> this.ErrorHandler e; null
            | :? IndexOutOfRangeException as e -> this.ErrorHandler e; null
    
    member this.Decrypt(data:string, ?pwd:string):byte[] = 
        this.Decrypt (Encoding.UTF8.GetBytes (data), (defaultArg pwd null))
    

    member this.EncryptFile(path:string, ?pwd:string):string = 
        let iv = this.RandomBytes lengthOfIV
        let salt = this.RandomBytes lengthOfSalt
        try
            let newPath = path + ".enc"
            use fs = new FileStream(newPath, FileMode.Create, FileAccess.Write) 
            fs.Write(salt, 0, lengthOfSalt)
            fs.Write(iv, 0, lengthOfIV)

            let AESkey, macKey = this.Keys(salt, (defaultArg pwd null))
            use cipher = this.Cipher(AESkey, iv)
            use ict = cipher.CreateEncryptor()
            use hmac = new HMACSHA256(macKey)
            hmac.TransformBlock(iv, 0, iv.Length, null, 0) |> ignore

            for data, fend in this.FileChunks(path) do
                let mutable ciphertext = Array.create data.Length 0uy

                if fend then
                    ciphertext <- ict.TransformFinalBlock(data, 0, data.Length)
                    hmac.TransformFinalBlock(ciphertext, 0, ciphertext.Length) |> ignore
                else
                    ict.TransformBlock(data, 0, data.Length, ciphertext, 0) |> ignore
                    hmac.TransformBlock(ciphertext, 0, ciphertext.Length, null, 0) |> ignore
                fs.Write(ciphertext, 0, ciphertext.Length)
            
            let mac = hmac.Hash
            fs.Write(mac, 0, mac.Length)
            newPath
        with 
            | :? ArgumentException as e -> this.ErrorHandler e; null
            | :? CryptographicException as e -> this.ErrorHandler e; null
            | :? UnauthorizedAccessException as e -> this.ErrorHandler e; null
            | :? FileNotFoundException as e -> this.ErrorHandler e; null
    
    member this.DecryptFile(path:string, ?pwd:string):string = 
        let salt = Array.create lengthOfSalt 0uy
        let iv = Array.create lengthOfIV 0uy
        let mac = Array.create lengthOfMAC 0uy

        try
            let newPath = Regex.Replace(path, ".enc$", ".dec")
            let fileSize = (int)(new FileInfo(path)).Length
            use fs = new FileStream(path, FileMode.Open, FileAccess.Read)

            fs.Read(salt, 0, lengthOfSalt) |> ignore
            fs.Read(iv, 0, lengthOfIV) |> ignore
            fs.Seek((int64)(fileSize - lengthOfMAC), SeekOrigin.Begin) |> ignore
            fs.Read(mac, 0, lengthOfMAC) |> ignore

            let AESkey, macKey = this.Keys(salt, (defaultArg pwd null))
            this.VerifyFile(path, mac, macKey)
        
            use fs = new FileStream(newPath, FileMode.Create, FileAccess.Write)
            use cipher = this.Cipher(AESkey, iv)
            use ict = cipher.CreateDecryptor()

            for data, fend in this.FileChunks(path, lengthOfSalt + lengthOfIV, lengthOfMAC) do
                let mutable plaintext = Array.create data.Length 0uy
                let mutable size = 0

                if fend then
                    plaintext <- ict.TransformFinalBlock(data, 0, data.Length)
                    size <- plaintext.Length
                else
                    size <- ict.TransformBlock(data, 0, data.Length, plaintext, 0)
                fs.Write(plaintext, 0, size)
            newPath
        with 
            | :? ArgumentException as e -> this.ErrorHandler e; null
            | :? CryptographicException as e -> this.ErrorHandler e; null
            | :? UnauthorizedAccessException as e -> this.ErrorHandler e; null
            | :? FileNotFoundException as e -> this.ErrorHandler e; null
    
    member this.SetMasterKey(key:byte[], ?raw:bool) =
        let mutable key = key
        try
            if not (defaultArg raw false) then
                key <- Convert.FromBase64String(Encoding.ASCII.GetString key)
            masterKey <- key
        with 
            | :? FormatException as e -> this.ErrorHandler e
    
    member this.SetMasterKey(key:string) =
        this.SetMasterKey((Encoding.ASCII.GetBytes key), false);

    member this.GetMasterKey(?raw:bool):byte[] =
        if masterKey = null then
            this.ErrorHandler (Exception "The key is not set!")
            null
        elif not (defaultArg raw false) then
            Encoding.ASCII.GetBytes (Convert.ToBase64String masterKey)
        else
            masterKey
    
    member this.RandomKeyGen(?lengthOfKey:int, ?raw:bool):byte[] =
        masterKey <- this.RandomBytes(defaultArg lengthOfKey 32)
        if (defaultArg raw false) then
            masterKey
        else
            Encoding.ASCII.GetBytes (Convert.ToBase64String masterKey)
    
    member private this.Keys(salt:byte[], ?pwd:string) = 
        let pwd = (defaultArg pwd null)
        let mutable dkey:byte[] = null

        if pwd <> null then
            dkey <- this.Pbkdf2Sha512(pwd, salt, lengthOfKey + lengthOfMACKey)
        elif masterKey <> null then
            dkey <- this.HkdfSha256(masterKey, salt, lengthOfKey + lengthOfMACKey)
        else
            raise (ArgumentException "No pwd or key specified!")
        dkey.[..lengthOfKey - 1], dkey.[lengthOfKey..]
    
    member private this.RandomBytes(size:int) =
        let rb = Array.create size 0uy
        use rng = new RNGCryptoServiceProvider()
        rng.GetBytes rb
        rb
    
    member private this.Cipher(key:byte[], iv:byte[]):RijndaelManaged =
        let rm =  new RijndaelManaged()
        rm.Mode <- modes.[mode]
        rm.Padding <- if mode = "CFB" then PaddingMode.None else PaddingMode.PKCS7
        rm.FeedbackSize <- if mode = "CFB" then 8 else 128
        rm.KeySize <- size
        rm.Key <- key
        rm.IV <- iv
        rm
    
    member private this.Sign(data:byte[], key:byte[]) = 
        use hmac = new HMACSHA256(key)
        hmac.ComputeHash data
    
    member private this.SignFile(path:string, key:byte[], ?fstart:int, ?fend:int) = 
        use hmac = new HMACSHA256(key)
        for data, _ in this.FileChunks(path, (defaultArg fstart 0), (defaultArg fend 0)) do 
            hmac.TransformBlock(data, 0, data.Length, null, 0) |> ignore
        hmac.TransformFinalBlock((Array.create 0 0uy), 0, 0) |> ignore
        hmac.Hash
    
    member private this.Verify(data, mac, key) = 
        let dataMac = this.Sign(data, key)
        if not (this.ConstantTimeComparison (mac, dataMac)) then
            raise (ArgumentException "MAC check failed!")
    
    member private this.VerifyFile(path:string, mac:byte[], key:byte[]) = 
        let fileMac = this.SignFile(path, key, lengthOfSalt, lengthOfMAC)
        if not (this.ConstantTimeComparison(mac, fileMac)) then
             raise (ArgumentException "MAC check failed!")
    
    member private this.ErrorHandler(e:Exception) =
        printfn "%s" e.Message
    
    member private this.ConstantTimeComparison(mac1:byte[], mac2:byte[]) =
        let mutable result = mac1.Length ^^^ mac2.Length
        for i in 0 .. (min mac1.Length mac2.Length) - 1 do
            result <- result ||| ((int)mac1.[i] ^^^ (int)mac2.[i])
        result = 0
     
    member private this.FileChunks(path:string, ?fbeg:int, ?fend:int):seq<Tuple<byte[], bool>> = 
        let mutable size = 1024
        let fs = new FileStream(path, FileMode.Open, FileAccess.Read)
        let fbeg = defaultArg fbeg 0
        let fend = (int)fs.Length - (defaultArg fend 0)
        let mutable pos = fs.Read(Array.create fbeg 0uy, 0, fbeg)

        seq { while pos < fend do
                size <- if fend - pos > size then size else fend - pos
                let data = Array.create size 0uy
                pos <- pos + fs.Read(data, 0, size)
                yield (data, pos = fend)
        }
    
    member private this.Pbkdf2Sha512(pwd:string, salt:byte[], dlengthOfKey:int):byte[] =
        let mutable dkey = Array.zeroCreate<byte> 0
        use prf = new HMACSHA512(Encoding.UTF8.GetBytes pwd)
        let hashLen = 64;

        for i in 0..hashLen..(dlengthOfKey - 1) do
            let b = Array.rev (BitConverter.GetBytes ((i / hashLen) + 1))
            let mutable u = prf.ComputeHash (Array.append salt b)
            let f = u

            for _ in 1..(this.keyIterations - 1) do
                u <- prf.ComputeHash u
                for k in 0..f.Length - 1 do
                    f.[k] <- f.[k] ^^^ u.[k]
            dkey <- Array.append dkey f
        dkey.[0..dlengthOfKey - 1]
    
    member private this.HkdfSha256(key:byte[], salt:byte[], dlengthOfKey:int):byte[] =
        let mutable dkey = Array.zeroCreate<byte> 0
        let mutable hkey = Array.zeroCreate<byte> 0
        let hashLen = 32;
        use prkHmac = new HMACSHA256(salt)
        let prk = prkHmac.ComputeHash key

        for i in 0..hashLen..(dlengthOfKey - 1) do
            hkey <- Array.append hkey [|(byte (i / hashLen + 1))|]
            use hmac = new HMACSHA256(prk)
            hkey <- hmac.ComputeHash hkey
            dkey <- Array.append dkey hkey
        dkey.[0..dlengthOfKey - 1]

let mutable i = 0
let mutable ii = 0
let obj = new Object()
let addIIByOne() =
    Monitor.Enter obj
    ii<- ii+1
    Monitor.Exit obj
    
let configuration = 
    ConfigurationFactory.ParseString(
        @"akka {
            log-config-on-start : on
            stdout-loglevel : DEBUG
            loglevel : ERROR
            actor {
                provider = ""Akka.Remote.RemoteActorRefProvider, Akka.Remote""
                debug : {
                    receive : on
                    autoreceive : on
                    lifecycle : on
                    event-stream : on
                    unhandled : on
                }
            }
            remote {
                helios.tcp {
                    port = 8123
                    hostname = localhost
                }
            }
        }")
let system = ActorSystem.Create("RemoteFSharp", configuration)

let echoServer = system.ActorSelection(
                            "akka.tcp://RemoteFSharp@localhost:8777/user/EchoServer")

let Aes = new AesEncryption("cbc", 256)

let encrypt (data2:string) = 
    let Ciphertext = Aes.Encrypt(data2, " ")
    let Cipherstring =Encoding.UTF8.GetString Ciphertext
    Cipherstring
let sendCmd cmd =
    let encrypt_message = encrypt cmd
    let json = " {\"command\":\"" + encrypt_message + "\"} "
    let response = Http.Request(
        "http://127.0.0.1:8080/twitter",
        httpMethod = "POST",
        headers = [ ContentType HttpContentTypes.Json ],
        body = TextRequest json
        )
    let response = string response.Body
    response

let rand = System.Random(1)
let akka_user_register (mailbox: Actor<_>) = 
    let rec loop () = actor {
        let! message = mailbox.Receive()
        let idx = message
        let mutable req = "new"           
        let mutable POST = " "
        let mutable user_name = "xyz"+(string idx)
        let mutable pwd = "!23456Abc" + (string idx)
        let mutable target_user_name = " "
        let mutable hash_mentioned = " "
        let mutable at = " "
        let mutable tweet_content = " "
        let mutable register = " "
        let cmd = req+","+user_name+","+pwd
        let response = sendCmd cmd
        printfn "%s" cmd
        printfn "%s" (string(response))
        printfn "%s" ""
        addIIByOne()
        return! loop()
    }
    loop ()
let akka_client_simulator (mailbox: Actor<_>) = 
    let rec loop () = actor {        
        let! message = mailbox.Receive ()
        let sender = mailbox.Sender()
        let idx = message
        match box message with
        | :? string   ->
            let mutable rand_num = Random( ).Next() % 7
            let mutable req = "new"           
            let mutable user_name = "xyz"+(string idx)
            let mutable pwd = "!23456Abc" + (string idx)
            let mutable target_user_name = "xyz"+rand.Next(N) .ToString()
            let mutable hash_mentioned = "#topic"+rand.Next(N) .ToString()
            let mutable at = "@xyz"+rand.Next(N) .ToString()
            let mutable tweet_content = "tweet"+rand.Next(N) .ToString()+" " + hash_mentioned + "" + at + " " 
            if rand_num=0 then  req <-"new"
            if rand_num=1 then  req <-"tweet"
            if rand_num=2 then  req <-"follow"
            if rand_num=3 then  req <-"retweet"
            if rand_num=4 then  req <-"twitterfeed"
            if rand_num=5 then  req <-"#"
            if rand_num=6 then  req <-"@" 
            // msg can be anything like "start"
            let cmd = req+","+user_name+","+pwd+","+target_user_name+","+tweet_content+","+hash_mentioned+","+at
            let response = sendCmd cmd
            printfn "%s" cmd
            printfn "%s" (string(response))
            printfn "%s" ""
            addIIByOne()
        return! loop()     
    }
    loop ()

let client_user_register = spawn system "client_user_register" akka_user_register    
let client_simulator = spawn system "client_simulator" akka_client_simulator


[<EntryPoint>]
let main (argv: string []): int = 
    printfn "%A" argv
    printfn "   Creating New Account   " 
    
    let stopWatch = System.Diagnostics.Stopwatch.StartNew()
    i<-0
    ii<-0
    while i<N do
        client_user_register <! string i |>ignore
        i<-i+1
    while ii<N-1 do
        Thread.Sleep(50)
    stopWatch.Stop()
    let time_register = stopWatch.Elapsed.TotalMilliseconds
        
    printfn "Tweet" 
    let stopWatch = System.Diagnostics.Stopwatch.StartNew()
    for i in 0..N-1 do
        for j in 0..10 do
            let cmd = "tweet,xyz"+(string i)+",!23456Abc"+(string i)+",tweet: xyz"+(string i)+"_"+(string j)+"th @xyz"+(string (rand.Next(N)))+" #topic"+(string (rand.Next(N)))
            let response = sendCmd cmd
            printfn "%s" cmd
            printfn "%s" (string(response))
            printfn "%s" ""
    stopWatch.Stop()
    let time_send = stopWatch.Elapsed.TotalMilliseconds
    
    
    
    
    
    let mutable step = 1
    let stopWatch = System.Diagnostics.Stopwatch.StartNew()
    printfn "Zipf Subscribe"  
    for i in 0..N-1 do
        for j in 0..step..N-1 do
            if not (j=i) then
                let cmd = "follow,xyz"+(string j)+",!23456Abc"+(string j)+",xyz"+(string i)
                let response = sendCmd cmd
                printfn "%s" cmd
                printfn "%s" (string(response))
                printfn "%s" ""
            step <- step+1
    stopWatch.Stop()
    let time_zipf_subscribe = stopWatch.Elapsed.TotalMilliseconds
        
    
    
    let stopWatch = System.Diagnostics.Stopwatch.StartNew()
    for i in 0..N-1 do
        let cmd = "twitterfeed,xyz"+(string i)+",!23456Abc"+(string i)
        let response = sendCmd cmd
        printfn "%s" cmd
        printfn "%s" (string(response))
        printfn "%s" ""
    stopWatch.Stop()
    let time_query = stopWatch.Elapsed.TotalMilliseconds
    
    
    
    let stopWatch = System.Diagnostics.Stopwatch.StartNew()
    for i in 0..N-1 do
        let cmd = "#,#topic"+(string (rand.Next(N)))
        let response = sendCmd cmd
        printfn "%s" cmd
        printfn "%s" (string(response))
        printfn "%s" ""
    stopWatch.Stop()
    let time_hashtag = stopWatch.Elapsed.TotalMilliseconds
    
    
    
    
    let stopWatch = System.Diagnostics.Stopwatch.StartNew()
    for i in 0..N-1 do
        let cmd = "@,@xyz"+(string (rand.Next(N)))
        let response = sendCmd cmd
        printfn "%s" cmd
        printfn "%s" (string(response))
        printfn "%s" ""
    stopWatch.Stop()
    let time_mention = stopWatch.Elapsed.TotalMilliseconds
    
    
    

    printfn " %d Tweeting with random operations  " M 
    let stopWatch = System.Diagnostics.Stopwatch.StartNew()
    i<-0
    ii<-0
    while i<M do
        client_simulator<! string (rand.Next(N)) |>ignore
        i <- i+1
    while ii<M-1 do
        Thread.Sleep(50)
    stopWatch.Stop()
    let time_random = stopWatch.Elapsed.TotalMilliseconds
    
    printfn "For %d users" N
    printfn "Creating: %f" time_register
    printfn "Tweet 10 msg: %f" time_send
    printfn "Zipf subscribe: %f" time_zipf_subscribe
    printfn "Query: %f" time_query
    printfn "Query Hashtags: %f" time_hashtag
    printfn "Query At: %f" time_mention
    printfn "Random operations: %f" time_random
    
    //printfn "Time taken: %f %f %f %f %f %f %f" time_register time_send time_zipf_subscribe time_query time_hashtag time_mention time_random

    
    system.Terminate() |> ignore
    0 // return an integer exit code