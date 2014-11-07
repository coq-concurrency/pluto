Require Import Coq.Lists.List.
Require Import FunctionNinjas.All.
Require Import Iterable.All.
Require Import ListString.All.
Require "MimeType".

Import ListNotations.

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
    Header.New Header.Kind.ContentLength (LString.of_N 10 12 None @@ Iterable.length content);
    Header.New Header.Kind.Server (LString.s "Coq")];
  body := content |}.

Definition error : t :=
  let mime_type := MimeType.New (LString.s "text") (LString.s "plain") in
  let content := LString.s "Error 404 (not found)." in
  {|
    status := Status.NotFound;
    headers := [
      Header.New Header.Kind.ContentType (MimeType.to_string mime_type);
      Header.New Header.Kind.ContentLength (LString.of_N 10 12 None @@ Iterable.length content);
      Header.New Header.Kind.Server (LString.s "Coq")];
    body := content |}.