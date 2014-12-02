(** Run some scenarios on Pluto. *)
Require Import Coq.Lists.List.
Require Import ListString.All.
Require Import Concurrency.Events.
Require Import Concurrency.Outputs.
Require Pluto.

Import ListNotations.

Definition answer_client_ok (client : ClientSocketId.t) (url : LString.t)
  (message : LString.t) : Run.t (Pluto.answer_client client url message) tt.
  eapply Run.Bind.
  exact (Run.Send Command.ClientSocketWrite (client, message) true).
  exact Run.Ret.
Defined.

Definition answer_client_error (client : ClientSocketId.t) (url : LString.t)
  (message : LString.t) : Run.t (Pluto.answer_client client url message) tt.
  eapply Run.Bind.
  exact (Run.Send Command.ClientSocketWrite (client, message) false).
  exact (Run.Send Command.Write _ tt).
Defined.

(*Program Definition handle_client (website_dir : LString.t)
  (client : ClientSocketId.t) (request : LString.t)
  : Run.t (Pluto.handle_client website_dir client (LString.s "") 1) tt :=
  Run.Bind _ (Run.Send Command.ClientSocketRead client (Some request)) (
  match Request.parse request with
  | inl (Request.New (Request.Method.Get, url, protocol) headers) =>
    Run.Bind tt (
      let url := website_dir ++ url in
      match Url.parse url with
      | inl (Url.New file_name _) => _
      | inr _ => _
      end)
      _
  | inr _ => _
  end).*)

(*Definition handle_client (website_dir : LString.t) (client : ClientSocketId.t)
  (request : LString.t) (fuel : nat)
  : Run.t (Pluto.handle_client website_dir client (LString.s "") fuel) tt.
  destruct fuel as [|fuel].
  - exact Run.Ret.
  - eapply Run.Bind.
    exact (Run.Send Command.ClientSocketRead client (Some request)).
    simpl; destruct (Request.parse request) as [request | ].*)
