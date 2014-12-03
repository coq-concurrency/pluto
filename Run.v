(** Run some scenarios on Pluto. *)
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.Ascii.
Require Import ListString.All.
Require Import Concurrency.Events.
Require Import Concurrency.Outputs.
Require Pluto.

Import ListNotations.
Local Open Scope char.

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

Definition handle_client (website_dir : LString.t) (client : ClientSocketId.t)
  (request : LString.t) (time : N) (content : option LString.t)
  : Run.t (Pluto.handle_client website_dir client) tt.
  eapply Run.Bind.
  exact (Run.Send Command.ClientSocketRead client (Some request)).
  refine (
    match Request.parse request with
    | inl (Request.New (Request.Method.Get, url, protocol) headers) => _
    | inr _ => _
    end).
  - eapply Run.Bind.
    exact (Run.Send Command.Time tt time).
    cbv zeta.
    destruct (Url.parse (website_dir ++ url)) as [parsed_url |].
    + destruct parsed_url as [file_name].
      eapply Run.Bind.
      exact (Run.Send Command.Write _ tt).
      eapply Run.Bind.
      exact (Run.Send Command.FileRead (Pluto.file_name_with_index file_name) content).
      apply answer_client_ok.
    + eapply Run.Bind.
      exact (Run.Send Command.Write _ tt).
      apply answer_client_ok.
  - exact Run.Ret.
Defined.

Definition print_usage : Run.t Pluto.print_usage tt :=
  Run.Send Command.Write _ tt.

Definition accept_clients_ok (website_dir : LString.t) (server : ServerSocketId.t)
  (client : ClientSocketId.t) (request : LString.t) (time : N)
  (content : option LString.t) : Run.t (Pluto.accept_clients website_dir server) tt.
  eapply Run.Bind.
  exact (Run.Send Command.ServerSocketAccept server (Some client)).
  eapply Run.Bind.
  exact (Run.Send Command.Write _ tt).
  exact (handle_client _ _ request time content).
Defined.

Definition program (path : LString.t) (port : LString.t) (website_dir : LString.t)
  (starting_time : N) (server : ServerSocketId.t) (client : ClientSocketId.t)
  (request : LString.t) (time : N) (content : option LString.t)
  : Run.t (Pluto.program [path; port; website_dir]) tt.
  unfold Pluto.program.
  destruct (LString.to_N 10 port) as [port_number|].
  - eapply Run.Bind.
    exact (Run.Send Command.Time tt starting_time).
    eapply Run.Bind.
    exact (Run.Send Command.Write _ tt).
    eapply Run.Bind.
    exact (Run.Send Command.ServerSocketBind port_number (Some server)).
    eapply Run.Bind.
    exact (Run.Send Command.Write _ tt).
    exact (accept_clients_ok website_dir server client request time content).
  - exact print_usage.
Defined.