Require Import Coq.Lists.List.
Require Import ListString.All.

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
  else if LString.eqb extension (LString.s "svg") then
    New (LString.s "image") (LString.s "svg+xml")
  else
    New (LString.s "text") (LString.s "plain").
