(* Alternative formatter.  *)
open Core

(* How many spaces for indentation.  *)
let indent = 2
(* Maximum width of a formatted line in characters.  *)
let width = 80

type formatted = Line of string | Multiline of string list

let flatten a b =
  match (a, b) with
  | Line a, Line b -> Multiline [a; b]
  | Line a, Multiline b -> Multiline (a :: b)
  | Multiline a, Line b -> Multiline (a @ [b])
  | Multiline a, Multiline b -> Multiline (a @ b)

let do_on_last ls f =
  match ls with
  | Line l -> Line (f l)
  | Multiline ls ->
     let rec g = function
       | [] -> []
       | [last] -> [f last]
       | h :: t -> h :: (g t)
     in
     Multiline (g ls)

let do_on_first ls f =
  match ls with
  | Line l -> Line (f l)
  | Multiline (h :: t) -> Multiline ((f h) :: t)
  | Multiline [] -> Multiline []
       
let make_indent amt = String.make amt ' '

let indent_str amt s =
  (make_indent amt) ^ s

(* Many different fragments of the AST can be formatted as a sequence of tokens
   with varying separators along with enclosing tokens, and all can be
   potentially rendered with the same basic logic.
   E.g.
     - A function header is enclosed by `let` and `=`, or `fun` and `->`.  Its
       tokens are separated by a single space, or newlines (`Multiline`).
       A type constructor in a binding is similarly enclosed by `type` and `=`,
       or in the case of an opaque type, `type` and the empty string.
     - A nested application of a function or type constructor is enclosed by `(`
       and `)`, with single-space separators.
     - Product types like tuples and records are enclosed by parens or braces,
       and use commas or semi-colons for separators.  In both single and
       multiline renders, whitespace follows the separator, and separators in
       multiline renderings lead each new line.
     - Value bindings in signatures are separated by `->` which in single line
       renderings is padded on both sides by whitespace, but in multiline
       situations renders as trailing each token with padding only on the left.

   All of this is fairly complex and leads to a lot of duplicated code, or
   something _potentially_ over-generalized.  I'm opting for the latter here.
 *)

type token_spacing = { left : int; right : int }

(* Where does the token go in a {! formatted.Multiline } situation?  *)
type token_behaviour =
  (* For separators, it should occur on the same line as the preceding token.
     For beginning enclosures, it should occur on the same line as the following.
   *)
  | Same_line of token_spacing
  (* Separators:  same line as the preceding token.
     Enclosures:  separate line from the preceding token.

     TODO:  these descriptions are *terrible*.  Maybe this type's semantics are
            all wrong.
   *)
  | Next_line of token_spacing

type spacing = { text : string
               ; single_line : token_spacing
               ; multi_line : token_behaviour
               }

type enclosure = { s : spacing
                 ; e : spacing
                 }
    
let spacing text single_line multi_line =
  { text; single_line; multi_line }

let spacing_size { text; single_line = { left; right }; _ } =
  (String.length text) + left + right
  
let single_ws_spacing =
  spacing "" { left = 0; right = 1 } (Next_line { left = 0; right = indent })

let no_spacing =
  spacing "" { left = 0; right = 0 } (Same_line { left = 0; right = 0 })

let no_enclosure =
  { s = no_spacing; e = no_spacing }

(* Configuration for complex nested expressions.

   Opening paren gets no spacing unless it's on the same line as the first
   token, in which case it gets one space on the right.
   Closing paren gets no spacing, but in multiline situations it goes on its
   own line.
   Separator is the empty string with single-space padding in single line
   renders and next-line double-indent for multline.

   Single line example:
     (function arg1 arg2)

   Multiline example:
     (function
       arg1
       arg2
     )
 *)
let nested_expr_config =
  let enc =
    { s = spacing "(" { left = 0; right = 0 } (Same_line { left = 0; right = 1 })
    ; e = spacing ")" { left = 0; right = 0 } (Next_line { left = 0; right = 0 })
    }
  in
  enc, single_ws_spacing

(* Returns two spacings, for the header (usable for an opaque binding) and body.
 *)
let type_binding_config =
  let header = 
    let enc =
      { s = spacing "type" { left = 0; right = 1 } (Same_line { left = 0; right = 1 })
      ; e = spacing "" { left = 0; right = 0 } (Same_line { left = 0; right = 1 })
      }
    in
    enc, single_ws_spacing
  in
  let body =
    let enc =
      { s = spacing "=" { left = 1; right = 1 } (Next_line { left = 0; right = 0 })
      ; e = no_spacing
      }
    in
    enc, single_ws_spacing
  in
  header, body

let val_bind_config =
  let val_part =
    let enc =
      { s = spacing "val" { left = 0; right = 1 } (Same_line { left = 0; right = 1 })
      ; e = no_spacing
      }
    in
    enc, single_ws_spacing
  in
  let def_part =
    let enc = { s = spacing ":" { left = 1; right = 1 } (Next_line { left = 0; right = 0 })
              ; e = no_spacing
              }
    in
    let spc = spacing "->" { left = 1; right = 1 } (Same_line { left = 1; right = 0 }) in
    enc, spc
  in
  val_part, def_part
  
let sig_config =
  let enc =
    { s = spacing "{" { left = 0; right = 1 } (Next_line { left = 0; right = 0 })
    ; e = spacing "}" { left = 1; right = 0 } (Next_line { left = 0; right = 0 })
    }
  in
  enc, single_ws_spacing

let spacer c =
  String.make c ' '

(* `seq` is a list of format functions that take an indentation amount in
   spaces, a remaining width, and return a formatted node.
 *)
let rec single_line_of_seq seq config indent rem_width =
  let make_spc { text; single_line = { left; right }; _ } =
    (spacer left) ^ text ^ (spacer right)
  in
  (* Start and end of the enclosure, then spacing.  *)
  let { s; e }, spacing = config in
  let prelude = indent_str indent (make_spc s) in
  (* Tie together all the rendered nodes with separators and the enclosure from
     the provided configuration.
   *)
  let complete rw xs =
    let postlude = make_spc e in
    match List.rev xs with
    | [] ->
       failwith "Trying to render an empty sequence."
    | h :: t ->
       let l = List.fold_left
                 (fun acc next -> acc ^ (make_spc spacing) ^ next)
                 (prelude ^ h)
                 t
       in
       Some (rw, Line (l ^ postlude))
  in
  let rec loop (rw, prev) rem_seq memo =
    match prev with
    | Line l when rw >= 0 ->
       begin
         match rem_seq with
         | []     -> complete rw (l :: memo)
         | h :: t -> loop (h 0 (rw - spacing_size spacing)) t (l :: memo)
       end
    (* Any multiline return from a formatting call needs to force fallback to
       multiline rendering.  Any situation where we've gone over the remaining
       width also means we need to fall back to multiline.
     *)
    | _ ->
       None

  in
  let init = (List.hd seq) 0 (rem_width - (String.length prelude)) in
  loop init (List.tl seq) []

and multi_line_of_seq seq config orig_indent rem_width =
  let { s; e }, spacing = config in
  let indent, rw, prelude = match s.multi_line with
    | Same_line { left; right } ->
       let init = (indent_str left s.text) ^ (spacer right) in
       let indent = (String.length init) +  orig_indent in
       let rw = rem_width - (String.length init) in
       begin
         match (List.hd seq) 0 (rem_width - (String.length s.text) - right) with
         | _, Line l ->
            indent, rw, Line (init ^ l)
         | _, Multiline (h :: t) ->
           ( indent
           , rw
           , Multiline ((init ^ h) :: (List.map (fun x -> indent_str indent x) t))
           )
         | _ ->
            failwith "multi_line_seq unreachable base case."
       end
    | Next_line { left; right } ->
       let init = Line (indent_str orig_indent ((spacer left) ^ s.text ^ (spacer right))) in
       let _, ls = (List.hd seq) orig_indent rem_width in
       orig_indent + indent, rem_width - 2, flatten init ls
  in

  let handle_sep (_, ls) =
    let ms { left; right } = (spacer left) ^ spacing.text ^ (spacer right) in
    match spacing.multi_line with
    | Next_line spc -> do_on_first ls (fun s -> (ms spc) ^ s)
    | Same_line spc -> do_on_last ls (fun s -> s ^ (ms spc))
  in

  let chunks = List.map (fun f -> handle_sep @@ f indent rw) (List.tl seq) in
  let without_end = List.fold_left (fun acc next -> flatten acc next) prelude chunks in
  let with_end = match e.multi_line with
    | Same_line { left; right } ->
       let f str = str ^ (spacer left) ^ e.text ^ (spacer right) in
       do_on_last without_end f
    | Next_line { left; right } ->
       let end_text = 
         indent_str indent (spacer left) ^ e.text ^ (spacer right)
       in
       flatten without_end (Line end_text)
  in
  rw, with_end

and seq_format seq config indent rem_width =
  match single_line_of_seq seq config indent rem_width with
  | Some res -> res
  | None -> multi_line_of_seq seq config indent rem_width

and indented_format ?config:(config = None) expr indent rem_width =
  let format_str n i w =
    w - (String.length n), Line (indent_str i n)
  in
  let format_te te i w =
    indented_format ~config:(Some nested_expr_config) (Type te) i w
  in
  match expr with
  | Type { n = TE_Bool; _ } ->
     rem_width - 4, Line (indent_str indent "bool")
  | Type { n = TE_Unit; _ } ->
     rem_width - 4, Line (indent_str indent "unit")
  | Type { n = Var v; _ } ->
     rem_width - (String.length v), Line (indent_str indent v)
  | Type { n = Named n; _ } ->
     rem_width - (String.length n), Line (indent_str indent n)
  | Type { n = TE_Apply ({ n; _ }, args); _ } ->
     let xs = List.map format_te args in
     let config = (Option.value config ~default:(no_enclosure, single_ws_spacing)) in
     seq_format ((format_str n) :: xs) config indent rem_width
  | Type { n = Signature ds; _ } ->
     let f = function
       | Opaque_type ({ n; _ }, args) ->
          let seq = (format_str n) :: (List.map format_te args) in
          fun i w -> seq_format seq (fst type_binding_config) i w
       | _ ->
          failwith "Can't format this signature member yet."
     in
     seq_format (List.map f ds) sig_config indent rem_width
  |_ ->
    failwith "Unsupported formatting."

let render ?width:(w = width) expr =
  match snd @@ indented_format expr 0 w with
  | Line s -> s
  | Multiline lines ->
     List.fold_left (fun acc next -> acc ^ "\n" ^ next) (List.hd lines) (List.tl lines)

