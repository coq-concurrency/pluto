Require Import ListString.All.

Definition extension (file_name : LString.t) : LString.t :=
  List.last (LString.split file_name ".") (LString.s "").
