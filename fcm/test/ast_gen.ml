(* Generation of AST fragments.
 *)
open QCheck

(* For formatting output.
   TODO:  probably should be using some of the stuff from stdlib using boxes,
   etc.
 *)
let width = 80

let list_gen g =
  let _small_small = Gen.list_size (Gen.int_bound 5) g in
  let _small_list = Gen.small_list g in
  _small_small

let first_valid =
  Gen.oneof [Gen.char_range 'A' 'Z'; Gen.char_range 'a' 'z']

let rem_valid =
  list_gen
 (Gen.oneof  [first_valid; Gen.numeral])

(* The included base/primitive types.  *)
let base_type =
  let open Fcm.Core in
  [TE_Unit; TE_Bool]

let label_gen =
  let chars = Gen.pair first_valid rem_valid in
  Gen.map (fun (a, b) -> Core.String.of_char_list (a :: b)) chars

(** { {0} Type Expression Generators }
 *)

let type_var_gen =
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

(* A generator to select between in-scope types and base (built-in) types.
 *)
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

(* TODO:
     - enable use of types from other signatures.
     - Generate (constructur, body) tuple rather than a signature-specific
       variant.

 *)
let transparent_gen arg_list =
  let open Gen in
  let open Fcm.Core in
  let type_from (name, args) =
    let non_node_args = (List.map (fun { n; _ } -> n) args) in
    map
      (fun t -> Transparent_type ((name, args), { n = t; pos = null_pos }))
      (available_gen [] non_node_args)
  in
  (* Re-use arg_list to synthesize a list of type variables.  *)
  (gen_label_and_nodes arg_list) >>= type_from

(* Signature type declaration generator.

   [ available_types ] is a list of {! Fcm.Core.type_constructor } instances.
 *)
let type_decl_gen available_types =
  let open Fcm.Core in
  let open Gen in
  let arg_list = list_gen type_var_gen in
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
    list_gen
 variant
  in

  oneof [opaque_gen; transparent_gen arg_list]

(* Value bindings in signatures.  *)
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
    (pair label_gen (list_gen
 available_type_nodes))

let sig_gen ?available_types:(available_types = []) =
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
    (Gen.small_int >>= (fun c -> f [] available_types c))

(** { {0} Term generators }
 *)

(** Anonymous functions/lambdas.  *)

(* TODO:
   - For elaboration:
     - Valid functions.
     - Valid functors, including signatures.
     - Invalid functions.

*)

(* Used for functor generation so that types explicit in a previous signature
   argument can be referenced directly.
 *)
let extract_types s =
  let open Fcm.Core in match s with
  | { n = Fcm.Core.Signature decls; _ } ->
     let open Fcm.Core in
     List.filter_map
       (function
        | Opaque_type c -> Some c
        | Transparent_type (c, _) -> Some c
        | Transparent_variants (c, _) -> Some c
        | _ -> None
       )
       decls
  | _ ->
     []

let rec valid_term available =
  let open Fcm.Core in
  let open Gen in
  let avail = map (fun t -> { n = t; pos = null_pos }) (oneofl available) in
  let core = [valid_fun_gen (); valid_functor_gen ()] in
  let full = if List.length available > 0 then (avail :: core) else core in
  let vt = oneof full in
  map (fun t -> Term t) vt

and valid_fun_gen _ =
  let open Gen in
  let open Fcm.Core in
  let base_gen = opt (available_gen [] []) in
  let p = pair (map (fun l -> Label l) label_gen) base_gen in
  let f (arg, arg_type) =
    (* TODO:  literals other than Unit.  *)
    let body = valid_term [arg; Unit] in
    let arg' = { n = arg; pos = null_pos } in
    let arg_type' = Option.map (fun x -> { n = x; pos = null_pos }) arg_type in
    let res = map
      (fun body -> { n = Fun ((Term arg', arg_type'), body); pos = null_pos })
      body
    in
    res
  in
  let x = p >>= f in
  x

and valid_functor_gen _ =
  let open Gen in
  let open Fcm.Core in
  let arg = sig_gen in
  let f =
    function
    | Type s ->
       let available_types = extract_types s in
       let body = sig_gen ~available_types in
       (* TODO:  better than no_arg, generate to remove ambiguity and clashes:  *)
       map
         (fun b ->
           { n = Fun ((Term { n = Label "no_arg"; pos = null_pos}, Some s), b)
           ; pos = null_pos
           }
         )
         body
    | _ ->
       failwith "Expected sig_gen to yield a type."
  in
  arg >>= f

(*
   TODO:  Expand to admit in-scope types.
 *)
let let_bind_gen _ =
  let open Gen in
  let open Fcm.Core in
  let f (name, e) =
    Let_bind ({ n = name; pos = null_pos }, e)
  in
  map f (pair label_gen (valid_term []))

let module_gen _ =
  let open Gen in
  let open Fcm.Core in
  let ts = list_gen (transparent_gen (list_gen type_var_gen)) in
  let bindings = list_gen (let_bind_gen ()) in
  let f (t, b) =
    let t' = List.filter_map
               (function
                | Transparent_type (c, e) -> Some (Type_decl (c, e))
                | _ -> None
               )
               t
    in
    { n = Mod (t' @ b); pos = null_pos }
  in
  map f (pair ts bindings)
