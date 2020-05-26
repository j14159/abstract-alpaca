type term = Unit
          | Var of string
          | Abs of (string * typ * term)
          | App of term * term
          | Type_abs of (string * term)
          | Type_app of term * typ
[@@deriving show]
and typ = TUnit
        | TVar of string
        | Arrow of typ * typ
        | Uni of string * typ
[@@deriving show]

let rec string_of_typ = function
  | TUnit -> "()"
  | TVar v -> v
  | Arrow (a, b) ->
     let str_a = match a with
       | Arrow (_, _) -> "(" ^ (string_of_typ a) ^ ")"
       | _ -> (string_of_typ a)
     in
      str_a ^ " -> " ^ (string_of_typ b)
  | Uni (v, t) -> "all[" ^ v ^ "]." ^ (string_of_typ t)

(* Stand-in for bounds and/or kinds later:  *)
type kind = unit

module Env : sig
  type t
  val create : unit -> t
  val bind_type : t -> string -> typ -> t
  val get_type : t -> string -> typ

  val bind_kind : t -> string -> kind -> t
  val get_kind : t -> string -> kind
end = struct
  type t_wrap = Typ of typ | Kind of kind
  type t = { context : (string * t_wrap) list
           }

  let create _ = { context = [] }

  let lookup_type t n =
    List.assoc_opt n t.context

  let bind_type t n e =
    match lookup_type t n with
    | Some _ -> failwith ("Can't redefine var " ^ n)
    | _ -> { context = (n, Typ e) :: t.context }

  (* At present this is just tracking the existence of type variables, not their
     actual kinds.
   *)
  let bind_kind t n _ =
    match lookup_type t n with
    | Some _ -> failwith ("Can't redefine type " ^ n)
    | _ -> { context = (n, Kind ()) :: t.context }

  let get_type t n =
    match lookup_type t n with
    | Some (Typ x) -> x
    | _ -> failwith (n ^ " is not bound to a type.")

  let get_kind t n =
    match lookup_type t n with
    | Some (Kind k) -> k
    | _ -> failwith ("Type variable " ^ n ^ " is not bound to a kind.  Missing abstraction?")

end

let validate_type env t =
  match t with
  | TVar v -> Env.get_kind env v
  | _ -> ()

let rec typ_of env expr =
  match expr with
  | Unit -> TUnit
  | Var n -> Env.get_type env n
  | Abs (v, t, body) ->
     validate_type env t;
     let env2 = Env.bind_type env v t in
     Arrow (t, typ_of env2 body)
  | App (t, arg) ->
     begin
     match (typ_of env t, typ_of env arg) with
     | Arrow (t1, ret_typ), t2 when t1 = t2 ->
        ret_typ
     | Arrow (t1, _), t2 ->
        let msg = (string_of_typ t2) ^ " does not match " ^ (string_of_typ t1)
                  ^ " in " ^ ([%derive.show: term] t) ^ " " ^ ([%derive.show: term] arg)
        in
        failwith  msg
     | _ ->
        let msg = "Cannot apply " ^ ([%derive.show: term] t)
                  ^ " to " ^ ([%derive.show: term] arg)
        in
        failwith msg
     end
  | Type_abs (v, body) ->
     let env2 = Env.bind_kind env v () in
     Uni (v, typ_of env2 body)
  | Type_app (term, ty) ->
     (* Beta reduction.  *)
     let apply_t_abs t =
       match typ_of env t with
       | Uni (v, _) ->
          let rec f = function
            | Abs (a, TVar vv, c) when vv = v -> Abs (a, ty, c)
            | Type_abs (_, t) -> f t
            | other -> other
          in
          f term
       | other ->
          let str_of_term = [%derive.show:term] term in
          failwith ("Cannot apply " ^ str_of_term ^ " to " ^ (string_of_typ other))
     in
     typ_of env (apply_t_abs term)


