Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import FunctionNinjas.All.
Require Import Iterable.All.
Require Import ListString.All.
Require Import Moment.All.
Require "MimeType".

Import ListNotations.
Local Open Scope string.
Local Open Scope list.

Module Status.
  Inductive t : Set :=
  | OK : t
  | NotFound : t.

  Definition code (status : t) : LString.t :=
    LString.s @@ match status with
    | OK => "200"
    | NotFound => "404"
    end.

  Definition message (status : t) : LString.t :=
    LString.s @@ match status with
    | OK => "OK"
    | NotFound => "Not Found"
    end.

  Definition to_string (status : t) : LString.t :=
    LString.join (LString.s " ") [LString.s "HTTP/1.1"; code status; message status].
End Status.

Module Header.
  Module Kind.
    Inductive t : Set :=
    | ContentType : t
    | ContentLength : t
    | Date : t
    | Server : t.

    Definition to_string (kind : t) : LString.t :=
      LString.s @@ match kind with
      | ContentType => "Content-Type"
      | ContentLength => "Content-Length"
      | Date => "Date"
      | Server => "Server"
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

Definition ok (mime_type : MimeType.t) (content : LString.t) (time : Moment.t)
  : t := {|
  status := Status.OK;
  headers := [
    Header.New Header.Kind.ContentType (MimeType.to_string mime_type);
    Header.New Header.Kind.ContentLength (LString.of_N 10 12 None @@ Iterable.length content);
    Header.New Header.Kind.Date (Moment.Print.rfc1123 time);
    Header.New Header.Kind.Server (LString.s "Coq")];
  body := content |}.

Definition error (time : Moment.t) : t :=
  let mime_type := MimeType.New (LString.s "text") (LString.s "plain") in
  let content := LString.s "Error 404 (not found)." in
  {|
    status := Status.NotFound;
    headers := [
      Header.New Header.Kind.ContentType (MimeType.to_string mime_type);
      Header.New Header.Kind.ContentLength (LString.of_N 10 12 None @@ Iterable.length content);
      Header.New Header.Kind.Date (Moment.Print.rfc1123 time);
      Header.New Header.Kind.Server (LString.s "Coq")];
    body := content |}.