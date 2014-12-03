(** The Pluto HTTP server. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Concurrency.Computation.
Require Import Concurrency.Events.
Require Import Moment.All.
Require Answer.
Require FileName.
Require Request.
Require Url.

Import ListNotations.
Import C.Notations.
Local Open Scope type.
Local Open Scope string.
Local Open Scope char.
Local Open Scope list.

(** Answer a message to a client. *)
Definition answer_client (client : ClientSocketId.t) (url : LString.t)
  (message : LString.t) : C.t unit :=
  let! is_success := C.Send Command.ClientSocketWrite (client, message) in
  if negb is_success then
    let message := LString.s "Answer failed to be sent for " ++ url in
    C.Send Command.Write message
  else
    C.Ret tt.

(** The answer to send to a client. *)
Definition answer (file_name : LString.t) (content : option LString.t)
  (time : N) : LString.t :=
  let time := Moment.of_epoch @@ Z.of_N time in
  Answer.to_string @@ match content with
  | None => Answer.error time
  | Some content =>
    let mime_type := MimeType.of_extension @@ FileName.extension file_name in
    Answer.ok mime_type content time
  end.

Definition file_name_with_index (file_name : LString.t) : LString.t :=
  let last_character := List.last file_name "/" in
  match last_character with
  | "/" => file_name ++ LString.s "index.html"
  | _ => file_name
  end.

(** Handle a client. *)
Definition handle_client (website_dir : LString.t) (client : ClientSocketId.t)
  : C.t unit :=
  let! request := C.Send Command.ClientSocketRead client in
  match request with
  | None =>
    (* We stop to listen to the socket in case of error. *)
    C.Send Command.Write (LString.s "The client is closed.")
  | Some request =>
    match Request.parse request with
    | inl (Request.New (Request.Method.Get, url, protocol) headers) =>
      let! time := C.Send Command.Time tt in
      let full_url := website_dir ++ url in
      match Url.parse full_url with
      | inl (Url.New file_name _) =>
        let file_name := file_name_with_index file_name in
        do! C.Send Command.Write (LString.s "Reading the file: '" ++ file_name ++ LString.s "'") in
        let! content := C.Send Command.FileRead file_name in
        answer_client client full_url @@ answer file_name content time
      | inr err =>
        let message := LString.s "In '" ++ full_url ++ LString.s "': " ++ err in
        do! C.Send Command.Write message in
        let time := Moment.of_epoch @@ Z.of_N time in
        answer_client client full_url @@ Answer.to_string @@ Answer.error time
      end
    | inr _ => C.Ret tt
    end
  end.

(** Display usage informations and quit. *)
Definition print_usage (_ : unit) : C.t unit :=
  let usage := LString.s "pluto port folder
  port: the port used by the server (like 80)
  folder: the folder of the website to serve" in
  C.Send Command.Write usage.

(** The loop to accept clients on the server socket. *)
Fixpoint accept_clients (website_dir : LString.t) (server : ServerSocketId.t)
  : C.t unit :=
  let! client := C.Send Command.ServerSocketAccept server in
  match client with
  | None => C.Send Command.Write (LString.s "Server socket failed.")
  | Some client =>
    do! C.Send Command.Write (LString.s "Client connected.") in
    handle_client website_dir client
  end.

(** The web server. *)
Definition program (argv : list LString.t) : C.t unit :=
  match argv with
  | [_; port; website_dir] =>
    match LString.to_N 10 port with
    | None => print_usage tt
    | Some port_number =>
      let! time := C.Send Command.Time tt in
      let time := Moment.Print.rfc1123 @@ Moment.of_epoch @@ Z.of_N time in
      let welcome_message := LString.s "Pluto starting on " ++ website_dir ++
        LString.s ", port " ++ port ++
        LString.s ", on " ++ time ++ LString.s "." in
      do! C.Send Command.Write welcome_message in
      let! server := C.Send Command.ServerSocketBind port_number in
      match server with
      | None => C.Send Command.Write (LString.s "The server socket cannot bind.")
      | Some server =>
        do! C.Send Command.Write (LString.s "Server socket bound.") in
        accept_clients website_dir server
      end
    end
  | _ => print_usage tt
  end.

(*(** * Extraction. *)
Require Import Concurrency.Extraction.

Definition pluto := Extraction.run Memory.Nil program.
Extraction "extraction/pluto" pluto.*)
