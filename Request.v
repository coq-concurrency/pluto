Require Import Coq.Lists.List.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import LString.All.

Import ListNotations.
Local Open Scope type.

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

(** For now, a request is supposed not to have a body. *)
Record t : Set := New {
  command : Command.t;
  headers : list Header.t }.

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
      inl @@ New command headers
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
    headers := [Header.New Header.Kind.Host (LString.s "example.com")] |} :=
  eq_refl.