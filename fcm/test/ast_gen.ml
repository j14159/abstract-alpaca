(* Generation of AST fragments.
 *)
open QCheck

(* For formatting output.
   TODO:  probably should be using some of the stuff from stdlib using boxes,
   etc.
 *)
let width = 80

let first_valid =
  Gen.oneof [Gen.char_range 'A' 'Z'; Gen.char_range 'a' 'z']

let rem_valid =
  Gen.small_list (Gen.oneof  [first_valid; Gen.numeral])

(* The included base/primitive types.  *)
let base_type =
  let open Fcm.Core in
  [TE_Unit; TE_Bool]

let label_gen =
  let chars = Gen.pair first_valid rem_valid in
  Gen.map (fun (a, b) -> Core.String.of_char_list (a :: b)) chars

let var_gen =
  Gen.map (fun l -> Fcm.Core.TE_Var ("'" ^ l) ) label_gen

(* Generate a label, e.g. a function name or type constructor name, followed
   by a list of nodes like type variables, types, etc.
 *)
let gen_label_and_nodes node_gen =
  let open Fcm.Core in
  let f (name, nodes) =
    let label = { n = name; pos = null_pos } in
    let nodes' = List.fold_right
                      (fun t_expr vs ->
                        { n = t_expr
                        ; pos = null_pos
                        } :: vs
                      )
                      nodes
                      []
    in
    label, nodes'
  in
  Gen.map f (Gen.pair label_gen node_gen)

(* TODO:  how to feed in known types?

   This could take input from a signature's preceding declarations or
   environment.
 *)
let type_apply_gen =
  (* Not quite correct, could have access to more types from the preceding
     definitions or import/open statements.
   *)
  let arg_list = Gen.small_list (Gen.oneof [var_gen; Gen.oneofl base_type]) in
  let open Fcm.Core in
  Gen.map (fun (name, args) -> TE_Apply (name, args)) (gen_label_and_nodes arg_list)

let available_gen available_types vars =
  let open Fcm.Core in
  let open Gen in
  let ag =
    let simple_types = vars @ base_type in
    let st_gen = oneofl simple_types in
    let arg_of_st = fun st -> { n = st; pos = null_pos } in
    (oneofl available_types) >>= (fun ({ n; _ }, args) ->
      let gen_list = List.map (fun _ -> map arg_of_st st_gen) args in
      map (fun args' -> TE_Apply ({ n; pos = null_pos}, args')) (flatten_l gen_list)
    )
  in
  if (List.length available_types > 0) then
    oneof [ag; oneofl base_type]
  else
    oneofl base_type

(* [ available_types ] is a list of {! Fcm.Core.type_constructor } instances.
   TODO:
   - Transparent gen.  Feed vars into definition.
 *)
let type_decl_gen available_types =
  let open Fcm.Core in
  let open Gen in
  let arg_list = small_list var_gen in
  let opaque_gen =
    map (fun (name, args) -> Opaque_type (name, args)) (gen_label_and_nodes arg_list)
  in
  let _variant_gen vars =
    (* TODO:  variants that take unit stand in for nullary variants here but
              I'm not sure that's good enough.
     *)
    let available_type_nodes = available_gen available_types vars in
    let arg = if (List.length vars > 0) then
                oneof [oneofl vars; available_type_nodes]
              else
                available_type_nodes
    in
    (* TODO:  real positions?  *)
    let variant =
      map
        (fun (l, t) -> ({ n = l; pos = null_pos }, { n = t; pos = null_pos }))
        (pair label_gen arg)
    in
    small_list variant
  in

  (* TODO:  enable use of types from other signatures.  *)
  let transparent_gen =
    (* Re-use arg_list to synthesize a list of type variables.  *)
    (gen_label_and_nodes arg_list)
    >>=
      (fun (name, args) ->
        let non_node_args = (List.map (fun { n; _ } -> n) args) in
        oneof [ (* Removing variants until I've thought through how to elaborate
                   them into F-omega.

                   map
                   (fun vs -> Transparent_variants ((name, args), vs))
                   (variant_gen non_node_args)
               ; *)map
                   (fun t -> Transparent_type ((name, args), { n = t; pos = null_pos }))
                   (available_gen [] non_node_args)
          ]
      )
  in
  oneof [opaque_gen; transparent_gen]
let val_bind_gen available_types =
  let open Fcm.Core in
  let open Gen in
  let available_type_nodes = available_gen available_types [] in
  map
    (fun (name, args) ->
      let args = List.map (fun x -> { n = x; pos = null_pos }) args in
      let body = match args with
        (* Can't have an empty value binding... *)
        | [] ->
           { n = TE_Unit; pos = null_pos }
        | h :: t ->
           List.fold_right (fun next acc -> { n = TE_Arrow (next, acc); pos = null_pos }) t h
      in
      Val_bind ( { n = name; pos = null_pos }
               , body)
    )
    (pair label_gen (small_list available_type_nodes))

let sig_gen =
  let open Fcm.Core in
  let extract memo = function
    | Opaque_type c -> c :: memo
    | Transparent_type (c, _) -> c :: memo
    | Transparent_variants (c, _) -> c :: memo
    | Val_bind _ -> memo
  in
  let rec f memo available c =
    if c < 0 then
      (* Gross...I'm sure I'm missing a much better way to do this.  *)
      Gen.oneofl [List.rev memo]
    else
      begin
        let next = Gen.oneof [type_decl_gen available; val_bind_gen available] in
        let open Gen in
        next >>= (fun x -> f (x :: memo) (extract available x) (c -1 ))
      end
  in
  let open Gen in
  map
    (fun ds -> Type ({ n = Signature ds; pos = null_pos }))
    (Gen.small_int >>= (fun c -> f [] [] c))
