(* Lots of this initially copied from the early stuff I did in
   https://github.com/j14159/basic_f
 *)

open Core

type formatted = Line of string | Multiline of string list

let flatten a b =
  match (a, b) with
  | Line a, Line b -> Multiline [a; b]
  | Line a, Multiline b -> Multiline (a :: b)
  | Multiline a, Line b -> Multiline (a @ [b])
  | Multiline a, Multiline b -> Multiline (a @ b)

let make_indent amt = String.make amt ' '

let indent_str amt s =
  (make_indent amt) ^ s

(* Turn a {!type:formatted} value into a {!type:string}.  *)
let render = function
  | Line s -> s
  | Multiline lines ->
     List.fold_left (fun acc next -> acc ^ "\n" ^ next) (List.hd lines) (List.tl lines)

(** Add a string prefix and suffix to a {!type:formatted} value.

    This is currently used only for binding and function nodes, since the
    formatter will split headers and bodies into either a multiline or single
    line value to which we then need to add a prefix like [let ] or [fun ] and a
    suffix such as [ ->] or [ = ].

    The name "bookend" because prefix and suffix are like bookends on a shelf.
 *)
let bookend first last lines =
  let rec f = function
    | [x] -> [x ^ last]
    | h :: tl -> h :: (f tl)
    | [] -> []
  in
  match lines with
  | Line l -> Line (first ^ l ^ last)
  | Multiline (hd :: tl) -> Multiline ((first ^  hd) :: (f tl))
  | other -> other

(** Partially re-sugars a !{type:Ast.node}'s arguments to simplify formatting.

    Oversimplified, this transforms [Fun (x, Fun (y, x))] to [([x; y], x)]
    which makes it much simpler to figure out the formatting of the arguments
    all together.
 *)
let expand_fun f =
  let rec expand f memo =
    match f with
    | { n = Fun (head, body); _ } -> expand body (head :: memo)
    | bottom -> (List.rev memo, bottom)
  in
  expand f []

  (* Function/binding headers are formatted separately from the body since there
   are two ways they may go multi-line:
   1. If the header (arguments, and name in the case of bindings) is too big
      to fit on one line.  In this case the arguments are distributed over
      multiple lines, and the arguments' first characters are aligned in the
      same column.
   2. If the body is too big to fit on the same line as the header.  In this
      case the body is placed on the line following the header, indented 2 more
      spaces.

   The implementation is disatisfying to me currently since it just tries to fit
   the header on a single line, and falls back to multi-line if it doesn't work
   out.  `single_line` and `multi_line` functions inside `format_fun_header` are
   basically just thunks to defer computation of multi-line headers until we
   know it's required.
 *)
let rec format_fun_header ?prefix:(prefix="fun ") ?sep:(sep="->") args indent rem_width =
  let single_line () =
    let buf = Buffer.create 100 in
    Buffer.add_string buf (make_indent indent);
    Buffer.add_string buf prefix;
    let rem_width' = rem_width - indent - (String.length prefix) in

    let f rem next =
      match indented_format next 0 rem with
      | (rem', Line next_s) ->
         Buffer.add_string buf next_s;
         Buffer.add_string buf " ";
         rem' - 1
      | _ -> failwith "Multiline format in single-line function header."
    in

    let rem = List.fold_left f rem_width' args in
    Buffer.add_string buf sep;
    (rem, Line (Bytes.to_string (Buffer.to_bytes buf)))
  in
  let multi_line () =
    let init = [(make_indent indent) ^ prefix ^ (snd (format (List.hd args) rem_width))] in
    let indent_amt = (indent + String.length prefix) in
    let form x =
      match indented_format x indent_amt rem_width with
      | (_, Line l) -> l
      | _ -> failwith "Can't support multi-line function arguments yet."
    in
    let rec folder xs memo =
      match xs with
      | h :: t -> folder t ((form h) :: memo)
      | [] ->
         let last_with_sep = (List.hd memo) ^ " " ^ sep in
         List.rev (last_with_sep :: (List.tl memo))
    in
    let buf = folder (List.tl args) init in
    (rem_width - 2, Multiline buf)
  in
  let (rem, _res) as res = single_line () in
  if rem > 0 then
    res
  else
    multi_line ()

(* Pieces together a function header and body.  `prefix` and `sep` are
   overridden for `let` bindings, with the default values set appropriately for
   function literals.
 *)
and format_fun ?prefix:(prefix="fun ") ?sep:(sep="->") args body_ast indent rem_width =
  let (rem_header, header) = format_fun_header ~prefix ~sep args indent rem_width in
  let (rem_body, body) = indented_format body_ast 0 rem_header in
  if rem_body <= 0 then
    begin
      let (rem, body) = indented_format body_ast (indent + 2) (rem_width - 2) in
      (rem, flatten header body)
    end
  else
    begin
      match header, body with
      (* Account for extra space:  *)
      | Line _, Line _ when rem_body >= 1 ->
         let full = (render header) ^ " " ^ (render body) in
         (rem_width - indent - String.length full, Line full)
      (* For now we give up and indent the body on the next line.  This could
         probably be improved, aesthetically.
       *)
      | _, _ ->
         let (rem_body, body) = indented_format body_ast (indent + 2) (rem_width - 2) in
         (rem_body, flatten header body)
    end

(* Main entry point for this module.

   This implementation is not terribly efficient because it generally tries
   to format things as a single line, falling back to multi-line if the single
   line rendering exceeds the available width.
 *)
and format expr rem_width =
  let rem, lines = indented_format expr 0 rem_width in
  (rem, render lines)

(* Remaining space (`rem_width`) and left margin (`indent`) separately tracked.

   How about indent and max width instead?  Otherwise maybe can't recover full
   intended width while recursing/unwinding.
 *)
and indented_format expr indent rem_width =
  match expr with
  | Type { n = TE_Bool; _ } ->
     rem_width - 4, Line (indent_str indent "bool")
  | Type { n = TE_Unit; _ } ->
     rem_width - 4, Line (indent_str indent "unit")
  | Type { n = Var v; _ } ->
     rem_width - (String.length v), Line (indent_str indent v)
  | Type { n = TE_Apply ({ n; _ }, args); _ } ->
     let constr_rw = rem_width - (String.length n) - 1 in
     let rw, rev_ls = List.fold_left
                    (fun (rw, xs) n ->
                      let rw', form_n = format (Type n) rw in
                      rw' - 1, form_n :: xs
                    )
                    (constr_rw, [indent_str indent n])
                    args
     in
     let ls = List.rev rev_ls in
     if rw >= 0 then
       rw, Line (List.fold_left (fun acc n -> acc ^ " " ^ n) "" ls)
     else
       begin
         match ls with
         | h :: t -> rem_width, Multiline (h :: List.map (fun x -> indent_str (indent + 2) x) t)
         | _ -> failwith "Type constructor format failure base case"
       end
  | _ ->
     failwith "Format not implemented."
