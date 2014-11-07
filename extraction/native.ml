let seq f g =
  f ();
  g ()

module String = struct
  let to_string s =
    let rec aux l i =
      if i = -1 then
        l
      else
        aux (s.[i] :: l) (i - 1) in
    aux [] (String.length s - 1)

  let of_string s =
    let length = List.length s in
    let buffer = String.create length in
    List.iteri (fun i c -> String.set buffer i c) s;
    buffer

  let append s1 s2 =
    s1 ^ s2

  let tokenize s =
    Str.split_delim (Str.regexp_string " ") s

  let is_empty s =
    String.length s = 0
end

module Process = struct
  type t = in_channel * out_channel

  let run = Unix.open_process

  let print_line message (_, output) =
    output_string output (message ^ "\n");
    flush output

  let fold_lines (input, _) state f =
    let rec aux state =
      match input_line input with
      | line ->
        (match f state line with
        | None -> ()
        | Some state -> aux state)
      | exception End_of_file -> () in
    aux state
end

module BigInt = struct
  let to_string = Big_int.string_of_big_int

  let of_string n =
    match Big_int.big_int_of_string n with
    | s -> Some s
    | exception _ -> None
end

let print_error message =
  prerr_endline message;
  flush stderr

let argv = Array.to_list Sys.argv
