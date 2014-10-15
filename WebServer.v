(** A simple HTTP web server. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import Iterable.All.
Require Import LString.All.
Require Import Concurrency.Computation.
Require Import Concurrency.Events.
Require Import Concurrency.StdLib.

Import ListNotations.
Import C.Notations.
Local Open Scope type.
Local Open Scope string.
Local Open Scope char.
Local Open Scope list.

Module MimeType.
  Record t : Set := New {
    type : LString.t;
    sub_type : LString.t }.

  Definition to_string (mime_type : t) : LString.t :=
    type mime_type ++ LString.s "/" ++ sub_type mime_type.

  Definition of_extension (extension : LString.t) : t :=
    if LString.eqb extension (LString.s "html") then
      New (LString.s "text") (LString.s "html")
    else if LString.eqb extension (LString.s "css") then
      New (LString.s "text") (LString.s "css")
    else if LString.eqb extension (LString.s "js") then
      New (LString.s "text") (LString.s "javascript")
    else if LString.eqb extension (LString.s "png") then
      New (LString.s "image") (LString.s "png")
    else
      New (LString.s "text") (LString.s "plain").
End MimeType.

Module FileName.
  Definition extension (file_name : LString.t) : LString.t :=
    List.last (LString.split file_name ".") (LString.s "").
End FileName.

Module Request.
  (** The kind of HTTP method. *)
  Module Method.
    (** For now, only the GET method is handled. *)
    Inductive t : Set :=
    | Get : t.

    Definition of_string (method : LString.t) : t + LString.t :=
      if LString.eqb method (LString.s "GET") then
        inl Get
      else
        inr (LString.s "unknown method " ++ method).
  End Method.

  Module Command.
    Definition t : Set := Method.t * LString.t * LString.t.

    Definition parse (command : LString.t) : t + LString.t :=
      match List.map LString.trim (LString.split (LString.trim command) " ") with
      | [method; arg1; arg2] =>
        Sum.bind (Method.of_string method) (fun method =>
        inl (method, arg1, arg2))
      | _ => inr @@ LString.s "three elements expected"
      end.
  End Command.

  Module Header.
    Module Kind.
      Inductive t : Set :=
      | Host : t.

      Definition of_string (kind : LString.t) : t + LString.t :=
        let kind := LString.down_case kind in
        if LString.eqb kind (LString.s "host") then
          inl Host
        else
          inr (LString.s "unknown header kind " ++ kind).
    End Kind.

    Record t : Set := New {
      kind : Kind.t;
      value : LString.t }.

    Definition parse (header : LString.t) : option t + LString.t :=
      match List.map LString.trim (LString.split_limit header ":" 2) with
      | [kind; value] =>
        match Kind.of_string kind with
        | inl kind => inl @@ Some @@ New kind value
        | inr _ => inl None
        end
      | _ => inr @@ LString.s "two elements expected"
      end.
  End Header.

  Record t : Set := New {
    command : Command.t;
    headers : list Header.t;
    body : LString.t }.

  Fixpoint parse_aux (command : Command.t) (headers : list Header.t)
    (lines : list LString.t) : t + LString.t :=
    match lines with
    | [] => inr @@ LString.s "empty line expected"
    | line :: lines =>
      let line := LString.trim line in
      if LString.is_empty line then
        let body := List.fold_left (fun s1 s2 =>
          s1 ++ LString.Char.n :: s2)
          lines [] in
        inl @@ New command headers body
      else
        Sum.bind (Header.parse line) (fun header =>
        let headers :=
          match header with
          | None => headers
          | Some header => header :: headers
          end in
        parse_aux command headers lines)
    end.

  Definition parse (request : LString.t) : t + LString.t :=
    let lines := LString.split request LString.Char.n in
    match lines with
    | [] => inr @@ LString.s "the request is empty"
    | command :: lines =>
      Sum.bind (Command.parse command) (fun command =>
      parse_aux command [] lines)
    end.

  Definition test_parse : parse @@ LString.s "GET /page.html HTTP/1.0
Host: example.com
Referer: http://example.com/
User-Agent: CERN-LineMode/2.15 libwww/2.17b3

" = inl {|
      command := (Method.Get, LString.s "/page.html", LString.s "HTTP/1.0");
      headers := [Header.New Header.Kind.Host (LString.s "example.com")];
      body := [LString.Char.n] |} :=
    eq_refl.
End Request.

Module Answer.
  Module Status.
    Inductive t : Set :=
    | OK : t
    | NotFound : t.

    Definition code (status : t) : LString.t :=
      match status with
      | OK => LString.s "200"
      | NotFound => LString.s "404"
      end.

    Definition message (status : t) : LString.t :=
      match status with
      | OK => LString.s "OK"
      | NotFound => LString.s "Not Found"
      end.

    Definition to_string (status : t) : LString.t :=
      LString.join (LString.s " ") [LString.s "HTTP/1.1"; code status; message status].
  End Status.

  Module Header.
    Module Kind.
      Inductive t : Set :=
      | ContentType : t
      | ContentLength : t
      | Server : t.

      Definition to_string (kind : t) : LString.t :=
        match kind with
        | ContentType => LString.s "Content-Type"
        | ContentLength => LString.s "Content-Length"
        | Server => LString.s "Server"
        end.
    End Kind.

    Record t : Set := New {
      kind : Kind.t;
      value : LString.t }.

    Definition to_string (header : t) : LString.t :=
      Kind.to_string (kind header) ++ LString.s ": " ++ value header.
  End Header.

  Record t : Set := New {
    status : Status.t;
    headers : list Header.t;
    body : LString.t }.

  Definition to_string (answer : t) : LString.t :=
    LString.join [LString.Char.n] (
      Status.to_string (status answer) ::
      List.map Header.to_string (headers answer) ++
      [LString.s ""; body answer]).

  Definition ok (mime_type : MimeType.t) (content : LString.t) : t := {|
    status := Status.OK;
    headers := [
      Header.New Header.Kind.ContentType (MimeType.to_string mime_type);
      Header.New Header.Kind.ContentLength (LString.of_n 10 12 @@ Iterable.length content);
      Header.New Header.Kind.Server (LString.s "Coq")];
    body := content |}.

  Definition error : t :=
    let mime_type := MimeType.New (LString.s "text") (LString.s "plain") in
    let content := LString.s "Error 404 (not found)." in
    {|
      status := Status.NotFound;
      headers := [
        Header.New Header.Kind.ContentType (MimeType.to_string mime_type);
        Header.New Header.Kind.ContentLength (LString.of_n 10 12 @@ Iterable.length content);
        Header.New Header.Kind.Server (LString.s "Coq")];
      body := content |}.
End Answer.

Definition handle_client (website_dir : LString.t) (client : ClientSocketId.t)
  : C.t [] unit :=
  do! Log.write (LString.s "Client connected.") (fun _ => C.Ret tt) in
  ClientSocket.read client [] (fun read request =>
  match request with
  | None => C.Ret None
  | Some line =>
    let read := line ++ read in
    match Request.parse read with
    | inl (Request.New (Request.Method.Get, url, protocol) headers body) =>
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
        ClientSocket.write client answer (fun _ =>
        ClientSocket.close client (fun is_closed =>
          let message := 
            if is_closed then
              LString.s "Client closed."
            else
              LString.s "Client cannot be closed." in
            Log.write message (fun _ => C.Ret tt)))) in
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