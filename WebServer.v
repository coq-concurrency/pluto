(** A simple HTTP web server. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import LString.All.
Require Import Concurrency.Computation.
Require Import Concurrency.Events.
Require Import Concurrency.StdLib.
Require "Answer".
Require "FileName".
Require "Request".

Import ListNotations.
Import C.Notations.
Local Open Scope type.
Local Open Scope string.
Local Open Scope char.
Local Open Scope list.

(** Read a file, trying to infer the implicit "index.html". *)
Definition read_file (client : ClientSocketId.t) (file_name : LString.t)
  (continuation : option (MimeType.t * LString.t) -> C.t [] unit)
  : C.t [] unit :=
  do! Log.write (LString.s "Reading the file: '" ++ file_name ++ LString.s "'")
    (fun _ => C.Ret tt) in
  File.read file_name (fun content =>
  match content with
  | None =>
    let file_name := file_name ++ LString.s "index.html" in
    do! Log.write (LString.s "Reading instead the file: '" ++ file_name ++
      LString.s "'") (fun _ => C.Ret tt) in
    File.read file_name (fun content =>
    match content with
    | None => continuation None
    | Some content =>
      let mime_type := MimeType.of_extension @@ FileName.extension file_name in
      continuation @@ Some (mime_type, content)
    end)
  | Some content =>
    let mime_type := MimeType.of_extension @@ FileName.extension file_name in
    continuation @@ Some (mime_type, content)
  end).

(** Answer to a client. *)
Definition handle_client (website_dir : LString.t) (client : ClientSocketId.t)
  : C.t [] unit :=
  do! Log.write (LString.s "Client connected.") (fun _ => C.Ret tt) in
  ClientSocket.read client [] (fun read request =>
  match request with
  | None =>
    do! Log.write (LString.s "The client is closed.") (fun _ => C.Ret tt) in
    C.Ret None (* We stop to listen to the socket in case of error. *)
  | Some line =>
    let read := read ++ line in
    match Request.parse read with
    | inl (Request.New (Request.Method.Get, url, protocol) headers) =>
      do! read_file client (website_dir ++ url) (fun reading =>
        let answer := Answer.to_string @@ match reading with
          | None => Answer.error
          | Some (mime_type, content) => Answer.ok mime_type content
          end in
        ClientSocket.write client answer (fun is_success =>
          if negb is_success then
            let message := LString.s "Answer failed to be sent for " ++ url in
            Log.write message (fun _ => C.Ret tt)
          else
            C.Ret tt)) in
      (* We continue to listen, starting again with empty data. *)
      C.Ret @@ Some []
    | inr err => C.Ret @@ Some read (* We wait for more data. *)
    end
  end).

(** The web server. *)
Definition program (argv : list LString.t) : C.t [] unit :=
  match argv with
  | [_; website_dir] =>
    Log.write (LString.s "Coq server starting on " ++ website_dir ++
      LString.s ".") (fun _ =>
    ServerSocket.bind 80 (fun client =>
      match client with
      | None =>
        Log.write (LString.s "Server socket failed.") (fun _ => C.Exit tt)
      | Some client => handle_client website_dir client
      end))
  | _ =>
    Log.write (LString.s "Exactly one parameter expected: the website folder.") (fun _ =>
    C.Exit tt)
  end.

(** * Extraction. *)
Require Import Extraction.

Definition http_server := Extraction.run _ Memory.Nil program.
Extraction "extraction/httpServer" http_server.