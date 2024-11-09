(*======================================================================

This is a self-contained SML implementation of Sockets. Typically used
to implement an Athena server that can be hit by arbitrary TCP clients
(see the file server.sml).

=======================================================================*)

structure Socket = struct

open TextIO

fun readAll conn req =
    let val ntoread = Socket.Ctl.getNREAD conn in
    if ntoread > 0
    then
    let
        val ntoreadMax1024x80 = if ntoread > 1024 * 80 then 1024 * 80 else ntoread;
        val vec = Socket.recvVec (conn, ntoreadMax1024x80);
        val vecLength = Word8Vector.length vec;
        val reqSoFar = req ^ (String.substring (Byte.bytesToString vec, 0, vecLength))
    in
        if vecLength < ntoreadMax1024x80
        then reqSoFar
        else readAll conn reqSoFar 
    end
    else req
    end;

fun makeServer(input_buffer_size,processRequest) = 
 fn port => 
   let fun run(listener) = let fun accept() = 
                                    let val (conn,conn_addr) = Socket.accept(listener)
	                                val text = readAll conn ""
                                    in
                                       respond(conn,text);                                      
                                       accept()
                                    end
                              and respond(conn,text) = let val reply = processRequest(text)
                                                           val buf = Word8VectorSlice.slice(Byte.stringToBytes reply,0,NONE)
                                                       in
                                                          ignore(Socket.sendVec(conn,buf));
                                                           Socket.close(conn)
                                                       end handle x => (Socket.close(conn);raise x)
                          in 
                             Socket.Ctl.setREUSEADDR(listener,true);
                             Socket.bind(listener,INetSock.any port);
                             Socket.listen(listener,9);
                             accept()
                          end handle x => (Socket.close(listener);raise x)
  in
    run(INetSock.TCP.socket())
  end handle e => (print("\nSomething went wrong" ^ (exnMessage e) ^ "\n");raise e)

end

