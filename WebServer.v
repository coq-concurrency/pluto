(** A simple HTTP web server. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Concurrency.Computation.
Require Import Concurrency.Events.
Require Import Concurrency.StdLib.
Require "Answer".
Require "FileName".
Require "Request".
Require "Url".

Import ListNotations.
Import C.Notations.
Local Open Scope type.
Local Open Scope string.
Local Open Scope char.
Local Open Scope list.

(** Answer a message to a client. *)
Definition answer_client (client : ClientSocketId.t) (url : LString.t)
  (message : LString.t) : C.t [] unit :=
  ClientSocket.write client message (fun is_success =>
  if negb is_success then
    let message := LString.s "Answer failed to be sent for " ++ url in
    Log.write message (fun _ => C.Ret tt)
  else
    C.Ret tt).

(** Handle a client. *)
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
      do!
        let url := website_dir ++ url in
        match Url.parse url with
        | inl (Url.New file_name _) =>
          let last_character := List.last file_name "/" in
          let file_name := match last_character with
            | "/" => file_name ++ LString.s "index.html"
            | _ => file_name
            end in
          do! Log.write (LString.s "Reading the file: '" ++ file_name ++ LString.s "'")
            (fun _ => C.Ret tt) in
          File.read file_name (fun content =>
          let answer := Answer.to_string @@ match content with
            | None => Answer.error
            | Some content =>
              let mime_type := MimeType.of_extension @@ FileName.extension file_name in
              Answer.ok mime_type content
            end in
          answer_client client url answer)
        | inr err =>
          let message := LString.s "In '" ++ url ++ LString.s "': " ++ err in
          do! Log.write message (fun _ => C.Ret tt) in
          answer_client client url @@ Answer.to_string Answer.error
        end in
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

Definition coq_web_server := Extraction.run _ Memory.Nil program.
Extraction "extraction/coqWebServer" coq_web_server.