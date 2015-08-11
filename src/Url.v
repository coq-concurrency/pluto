Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import ListString.All.

Import ListNotations.
Local Open Scope char.

Record t : Set := New {
  name : LString.t;
  arguments : list (LString.t * LString.t) }.

Fixpoint parse_arguments (arguments : list LString.t)
  : list (LString.t * LString.t) + LString.t :=
  match arguments with
  | [] | [[]] => inl []
  | argument :: arguments =>
    match LString.split argument "=" with
    | [k; v] =>
      Sum.bind (parse_arguments arguments) (fun arguments =>
      inl ((k, v) :: arguments))
    | _ => inr @@ LString.s "expected exactly one '=' sign"
    end
  end.

Definition parse (url : LString.t) : t + LString.t :=
  match LString.split url "?" with
  | [name] => inl @@ New name []
  | [name; arguments] =>
    Sum.bind (parse_arguments @@ LString.split arguments "&") (fun arguments =>
    inl @@ New name arguments)
  | _ => inr @@ LString.s "expected at most one question mark"
  end.

Module Test.
  Import LString.

  Definition test_parse : List.map parse [
    s "test/";
    s "test/index.html";
    s "test/index.html?";
    s "test/index.html?x=3";
    s "test/index.html?x=3&y=42"] = [
    inl @@ New (s "test/") [];
    inl @@ New (s "test/index.html") [];
    inl @@ New (s "test/index.html") [];
    inl @@ New (s "test/index.html") [(s "x", s "3")];
    inl @@ New (s "test/index.html") [(s "x", s "3"); (s "y", s "42")]] :=
    eq_refl.
End Test.