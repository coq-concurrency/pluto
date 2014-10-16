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
Require "Request".

Import ListNotations.
Import C.Notations.
Local Open Scope type.
Local Open Scope string.
Local Open Scope char.
Local Open Scope list.

Module FileName.
  Definition extension (file_name : LString.t) : LString.t :=
    List.last (LString.split file_name ".") (LString.s "").
End FileName.

Definition close_client (client : ClientSocketId.t) : C.t [] unit :=
  ClientSocket.close client (fun is_closed =>
  let message :=
    if is_closed then
      LString.s "Client closed."
    else
      LString.s "Client cannot be closed." in
  Log.write message (fun _ => C.Ret tt)).

Definition handle_client (website_dir : LString.t) (client : ClientSocketId.t)
  : C.t [] unit :=
  do! Log.write (LString.s "Client connected.") (fun _ => C.Ret tt) in
  ClientSocket.read client [] (fun read request =>
  match request with
  | None => C.Ret None
  | Some line =>
    let read := line ++ read in
    match Request.parse read with
    | inl (Request.New (Request.Method.Get, url, protocol) headers) =>
      do!
        let file_name := website_dir ++ url in
        do! Log.write (LString.s "Reading file: '" ++ file_name ++
          LString.s "'") (fun _ => C.Ret tt) in
        File.read file_name (fun content =>
        let answer := Answer.to_string @@ match content with
          | None => Answer.error
          | Some content =>
            let mime_type := MimeType.of_extension @@ FileName.extension url in
            Answer.ok mime_type content
          end in
        ClientSocket.write client answer (fun is_success =>
          do! if negb is_success then
            let message := LString.s "Answer failed to be sent for " ++ url in
            Log.write message (fun _ => C.Ret tt)
          else
            C.Ret tt in
          close_client client)) in
      C.Ret @@ Some []
    | inr _ => C.Ret @@ Some read
    end
  end).

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