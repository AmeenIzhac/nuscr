open! Base
open Printf
open Loc
open Err
open Names

type scr_module = Syntax.scr_module

type global_protocol = Syntax.global_protocol

(** Various definitions and operations on Payload *)
module Payload = struct
  type payload =
    | PValue of VariableName.t option * Expr.payload_type
    | PDelegate of ProtocolName.t * RoleName.t
  [@@deriving sexp_of]

  (* Ignoring variable names for now *)
  let equal_payload p1 p2 =
    match (p1, p2) with
    | PValue (_, n1), PValue (_, n2) -> Expr.equal_payload_type n1 n2
    | PDelegate (pn1, rn1), PDelegate (pn2, rn2) ->
        ProtocolName.equal pn1 pn2 && RoleName.equal rn1 rn2
    | _, _ -> false

  let equal_pvalue_payload p1 p2 =
    let var_name_equal = Option.equal VariableName.equal in
    match (p1, p2) with
    | PValue (v1, n1), PValue (v2, n2) ->
        var_name_equal v1 v2 && Expr.equal_payload_type n1 n2
    | _ -> equal_payload p1 p2

  let compare_payload p1 p2 =
    match (p1, p2) with
    | PValue (_, ptn1), PValue (_, ptn2) ->
        Expr.compare_payload_type ptn1 ptn2
    | PValue _, PDelegate _ -> -1
    | PDelegate _, PValue _ -> 1
    | PDelegate (pn1, rn1), PDelegate (pn2, rn2) ->
        let comp_fst = ProtocolName.compare pn1 pn2 in
        if comp_fst = 0 then RoleName.compare rn1 rn2 else comp_fst

  let show_payload = function
    | PValue (var, ty) ->
        let var =
          match var with
          | Some var -> VariableName.user var ^ ": "
          | None -> ""
        in
        sprintf "%s%s" var (Expr.show_payload_type ty)
    | PDelegate (proto, role) ->
        sprintf "%s @ %s" (ProtocolName.user proto) (RoleName.user role)

  let pp_payload fmt p = Caml.Format.fprintf fmt "%s" (show_payload p)

  let of_syntax_payload (payload : Syntax.payloadt) =
    let open Syntax in
    match payload with
    | PayloadName n -> PValue (None, Expr.parse_typename n)
    | PayloadDel (p, r) -> PDelegate (p, r)
    | PayloadBnd (var, n) -> PValue (Some var, Expr.parse_typename n)
    | PayloadRTy (Simple n) -> PValue (None, Expr.parse_typename n)
    | PayloadRTy (Refined (v, t, e)) ->
        if Pragma.refinement_type_enabled () then
          PValue (Some v, Expr.PTRefined (v, Expr.parse_typename t, e))
        else
          uerr
            (PragmaNotSet
               ( Pragma.show Pragma.RefinementTypes
               , "Refinement Types require RefinementTypes pramga to be set."
               ) )

  let typename_of_payload = function
    | PValue (_, ty) -> Expr.payload_typename_of_payload_type ty
    | PDelegate _ ->
        Err.unimpl ~here:[%here] "delegation for code generation"
end

include Payload

type message = {label: LabelName.t; payload: payload list}
[@@deriving eq, sexp_of, ord]

let show_message {label; payload} =
  sprintf "%s(%s)" (LabelName.user label)
    (String.concat ~sep:", " (List.map ~f:show_payload payload))

let pp_message fmt m = Caml.Format.fprintf fmt "%s" (show_message m)

let of_syntax_message (message : Syntax.message) =
  let open Syntax in
  match message with
  | Message {name; payload} ->
      {label= name; payload= List.map ~f:of_syntax_payload payload}
  | MessageName name -> {label= name; payload= []}

type rec_var =
  { rv_name: VariableName.t
  ; rv_roles: RoleName.t list
  ; rv_ty: Expr.payload_type
  ; rv_init_expr: Expr.t }
[@@deriving sexp_of, eq]

let show_rec_var {rv_name; rv_roles; rv_ty; rv_init_expr} =
  sprintf "%s<%s>: %s = %s"
    (VariableName.user rv_name)
    (String.concat ~sep:", " (List.map ~f:RoleName.user rv_roles))
    (Expr.show_payload_type rv_ty)
    (Expr.show rv_init_expr)

type t =
  | MessageG of message * RoleName.t * RoleName.t * t
  | MuG of TypeVariableName.t * rec_var list * t
  | TVarG of TypeVariableName.t * Expr.t list * (t Lazy.t[@sexp.opaque])
  | ChoiceG of RoleName.t * t list
  | EndG
  | CallG of RoleName.t * ProtocolName.t * RoleName.t list * t
[@@deriving sexp_of]

let rec evaluate_lazy_gtype = function
  | MessageG (m, r1, r2, g) -> MessageG (m, r1, r2, evaluate_lazy_gtype g)
  | MuG (tv, rv, g) -> MuG (tv, rv, evaluate_lazy_gtype g)
  | TVarG (tv, es, g) ->
      TVarG
        ( tv
        , es
        , (* Force evaluation, then convert back to a lazy value *)
          Lazy.from_val (Lazy.force g) )
  | ChoiceG (r, gs) -> ChoiceG (r, List.map ~f:evaluate_lazy_gtype gs)
  | EndG -> EndG
  | CallG (r, p, rs, g) -> CallG (r, p, rs, evaluate_lazy_gtype g)

type nested_global_info =
  { static_roles: RoleName.t list
  ; dynamic_roles: RoleName.t list
  ; nested_protocol_names: ProtocolName.t list
  ; gtype: t }

type nested_t = nested_global_info Map.M(ProtocolName).t

let show =
  let indent_here indent = String.make (indent * 2) ' ' in
  let rec show_global_type_internal indent =
    let current_indent = indent_here indent in
    function
    | MessageG (m, r1, r2, g) ->
        sprintf "%s%s from %s to %s;\n%s" current_indent (show_message m)
          (RoleName.user r1) (RoleName.user r2)
          (show_global_type_internal indent g)
    | MuG (n, rec_vars, g) ->
        let rec_vars_s =
          if List.is_empty rec_vars then ""
          else
            "["
            ^ String.concat ~sep:", " (List.map ~f:show_rec_var rec_vars)
            ^ "] "
        in
        sprintf "%srec %s %s{\n%s%s}\n" current_indent
          (TypeVariableName.user n) rec_vars_s
          (show_global_type_internal (indent + 1) g)
          current_indent
    | TVarG (n, rec_exprs, _) ->
        let rec_exprs_s =
          if List.is_empty rec_exprs then ""
          else
            " ["
            ^ String.concat ~sep:", " (List.map ~f:Expr.show rec_exprs)
            ^ "]"
        in
        sprintf "%scontinue %s%s;\n" current_indent (TypeVariableName.user n)
          rec_exprs_s
    | EndG -> "" (* was previously: sprintf "%send\n" current_indent *)
    | ChoiceG (r, gs) ->
        let pre =
          sprintf "%schoice at %s {\n" current_indent (RoleName.user r)
        in
        let intermission = sprintf "%s} or {\n" current_indent in
        let post = sprintf "%s}\n" current_indent in
        let choices =
          List.map ~f:(show_global_type_internal (indent + 1)) gs
        in
        let gs = String.concat ~sep:intermission choices in
        pre ^ gs ^ post
    | CallG (caller, proto_name, roles, g) ->
        sprintf "%s%s calls %s(%s);\n%s" current_indent
          (RoleName.user caller)
          (ProtocolName.user proto_name)
          (String.concat ~sep:", " (List.map ~f:RoleName.user roles))
          (show_global_type_internal indent g)
  in
  show_global_type_internal 0

let call_label caller protocol roles =
  let str_roles = List.map ~f:RoleName.user roles in
  let roles_str = String.concat ~sep:"," str_roles in
  (* Current label is a bit arbitrary - find better one? *)
  let label_str =
    sprintf "call(%s, %s(%s))" (RoleName.user caller)
      (ProtocolName.user protocol)
      roles_str
  in
  LabelName.create label_str (ProtocolName.where protocol)

let show_nested_t (g : nested_t) =
  let show_aux ~key ~data acc =
    let {static_roles; dynamic_roles; nested_protocol_names; gtype} = data in
    let str_proto_names =
      List.map ~f:ProtocolName.user nested_protocol_names
    in
    let names_str = String.concat ~sep:", " str_proto_names in
    let proto_str =
      sprintf "protocol %s(%s) {\n\nNested Protocols: %s\n\n%s\n}"
        (ProtocolName.user key)
        (Symtable.show_roles (static_roles, dynamic_roles))
        (if String.length names_str = 0 then "-" else names_str)
        (show gtype)
    in
    proto_str :: acc
  in
  String.concat ~sep:"\n\n" (List.rev (Map.fold ~init:[] ~f:show_aux g))

let rec_var_of_syntax_rec_var rec_var =
  let open Syntax in
  let {var; roles; ty; init} = rec_var in
  let rv_ty =
    match of_syntax_payload ty with
    | PValue (_, ty) -> ty
    | _ -> assert false
  in
  {rv_name= var; rv_roles= roles; rv_ty; rv_init_expr= init}

type conv_env =
  { free_names: Set.M(TypeVariableName).t
  ; lazy_conts:
      (t * Set.M(TypeVariableName).t) Lazy.t Map.M(TypeVariableName).t
  ; unguarded_tvs: Set.M(TypeVariableName).t }

let init_conv_env =
  { free_names= Set.empty (module TypeVariableName)
  ; lazy_conts= Map.empty (module TypeVariableName)
  ; unguarded_tvs= Set.empty (module TypeVariableName) }

let of_protocol (global_protocol : Syntax.global_protocol) =
  let open Syntax in
  let {Loc.value= {roles; interactions; _}; _} = global_protocol in
  let assert_empty l =
    if not @@ List.is_empty l then
      unimpl ~here:[%here] "Non tail-recursive protocol"
  in
  let check_role r =
    if not @@ List.mem roles r ~equal:RoleName.equal then
      uerr @@ UnboundRole r
  in
  let rec conv_interactions env (interactions : global_interaction list) =
    match interactions with
    | [] -> (EndG, env.free_names)
    | {value; _} :: rest -> (
      match value with
      | MessageTransfer {message; from_role; to_roles; _} ->
          check_role from_role ;
          let init, free_names =
            conv_interactions
              {env with unguarded_tvs= Set.empty (module TypeVariableName)}
              rest
          in
          let f to_role acc =
            check_role to_role ;
            if RoleName.equal from_role to_role then
              uerr
                (ReflexiveMessage
                   ( from_role
                   , RoleName.where from_role
                   , RoleName.where to_role ) ) ;
            MessageG (of_syntax_message message, from_role, to_role, acc)
          in
          (List.fold_right ~f ~init to_roles, free_names)
      | Recursion (rname, rec_vars, interactions) ->
          if Set.mem env.free_names rname then
            unimpl ~here:[%here] "Alpha convert recursion names"
          else assert_empty rest ;
          let rec lazy_cont =
            lazy
              (conv_interactions
                 { env with
                   lazy_conts=
                     Map.add_exn ~key:rname ~data:lazy_cont env.lazy_conts
                 ; unguarded_tvs= Set.add env.unguarded_tvs rname }
                 interactions )
          in
          let rec_vars =
            if Pragma.refinement_type_enabled () then
              List.map ~f:rec_var_of_syntax_rec_var rec_vars
            else []
          in
          List.iter
            ~f:(fun {rv_roles; _} -> List.iter ~f:check_role rv_roles)
            rec_vars ;
          let cont, free_names_ = Lazy.force lazy_cont in
          (* Remove degenerate recursion here *)
          if Set.mem free_names_ rname then
            (MuG (rname, rec_vars, cont), Set.remove free_names_ rname)
          else (cont, free_names_)
      | Continue (name, rec_exprs) ->
          let rec_exprs =
            if Pragma.refinement_type_enabled () then rec_exprs else []
          in
          if Set.mem env.unguarded_tvs name then
            uerr (UnguardedTypeVariable name) ;
          let cont =
            lazy (Lazy.force (Map.find_exn env.lazy_conts name) |> fst)
          in
          assert_empty rest ;
          (TVarG (name, rec_exprs, cont), Set.add env.free_names name)
      | Choice (role, interactions_list) ->
          assert_empty rest ;
          check_role role ;
          if List.length interactions_list = 1 then
            (* Remove degenerate choice *)
            let interaction = List.hd_exn interactions_list in
            conv_interactions env interaction
          else
            let conts = 
              List.map ~f:(conv_interactions env) interactions_list
            in
            ( ChoiceG (role, List.map ~f:fst conts)
            , Set.union_list
                (module TypeVariableName)
                (List.map ~f:snd conts) )
      | Do (protocol, roles, _) ->
          (* This case is only reachable with NestedProtocols pragma turned on
           * *)
          assert (Pragma.nested_protocol_enabled ()) ;
          let fst_role = List.hd_exn roles in
          let cont, free_names =
            conv_interactions
              {env with unguarded_tvs= Set.empty (module TypeVariableName)}
              rest
          in
          (CallG (fst_role, protocol, roles, cont), free_names)
          | Calls (caller, proto, roles, _) ->
          let cont, free_names =
            conv_interactions
              {env with unguarded_tvs= Set.empty (module TypeVariableName)}
              rest
          in
          (CallG (caller, proto, roles, cont), free_names) )
  in
  let gtype, free_names = conv_interactions init_conv_env interactions in
  match Set.choose free_names with
  | Some free_name -> uerr (UnboundRecursionName free_name)
  | None -> evaluate_lazy_gtype gtype
  
module CrashPattern = struct

(* some variable naming i have used:
   t for type
   gp for global protocol
   e for element
   l for list
   r for role
   p for participant (i should probably go rename all rs to ps or vice versa as they represent the same thing)
   c for choice *)

(* gets the head of a list *)
let head l =
  match l with
    | [] -> failwith "head failed: list was empty"
    | e :: _ -> e

(* remove_last removes the last item from a list *)
let rec remove_last l = 
  match l with
    | [] -> failwith "reomve_last failed: expected a non empty list"
    | [_] -> []
    | e :: es -> e :: remove_last es 

(* get_last returns the last item in a list *)
let rec get_last l =
  match l with
    | [] -> failwith "get_last failed: expected a non empty list"
    | [e] -> e
    | _ :: es -> get_last es

(* foldl is just the standard fold left. the return type of List.fold_left was very weird for some reason so i 
   reimplemented it *)
let rec foldl f z list =
  match list with
    | [] -> z
    | x :: xs -> foldl f (f z x) xs

(* messages_equal compares two message labels and determines whether they are equal *)
let labels_equal msg msg' = 
  let {label = l ; payload = _} = msg in 
    let {label = l' ; payload = _} = msg' in 
      if (LabelName.compare l l') = 0 then true else false

(* roles_equal compares two roles and determines whether they are equal *)
let roles_equal r1 r2 = if (RoleName.compare r1 r2) = 0 then true else false
    
(* role_elem takes a role and a list of roles and determines whether r is an element of rs *)
let rec role_elem r rs = 
  match rs with
    | [] -> false
    | r' :: rs' -> if roles_equal r r' then true else role_elem r rs'

(* roles_subset takes a set of roles rs1 and another set rs2 and returns true iff rs1 is a subset of rs2 *)
let rec roles_subset rs1 rs2 = 
  match rs1 with
    | [] -> true
    | [r] -> role_elem r rs2
    | r :: rs -> role_elem r rs2 && roles_subset rs rs2

(* nub_roles takes a list of roles and removes any duplicate role names leaving a list of unique role names *)
let rec nub_roles l =
  match l with
    | [] -> []
    | (r :: rs) -> if (role_elem r rs) then (nub_roles rs) else (r :: nub_roles rs)

(* all_roles_equal takes two lists of roles, makes sets of them to remove duplicates, then returns true if
   the roles they contain are the same *)
let all_roles_equal rs1 rs2 = 
  let rs1' = nub_roles rs1 in
    let rs2' = nub_roles rs2 in
      roles_subset rs1' rs2' && roles_subset rs2' rs1'

(* type_vars_equal compares two type variables and determines whether they are equal *)
let type_vars_equal t1 t2 = if (TypeVariableName.compare t1 t2) = 0 then true else false

(* roles will take a global protocol and return a list of unique roles involved in that protocol *)
let rec roles t = nub_roles (roles' t)
  and roles' t =
    match t with
      | MessageG (_, from_role, to_role, t) -> from_role :: to_role :: roles' t
      | MuG (_, _, t) -> roles' t 
      | ChoiceG (role, choices) -> role :: List.concat (List.map choices ~f:roles')
      | CallG (_, _, roles, _) -> roles
      | _ -> []

(* apply_to_every_choice will take a function f, recurse through a type t and apply the f to every choice in t *)
let rec apply_to_every_choice f t =
  match t with
    | MessageG (msg, sender, receiver, t) -> MessageG (msg, sender, receiver, apply_to_every_choice f t) 
    | MuG (type_var, rec_vars, g) -> MuG (type_var, rec_vars, apply_to_every_choice f g)
    | ChoiceG (name, ts) -> f (ChoiceG (name, List.map ts ~f:(apply_to_every_choice f)))
    | CallG (caller, protocol, participants, t) -> CallG (caller, protocol, participants, apply_to_every_choice f t)
    | e -> e

(* desguar takes all messages and turns them into choices so that we can add crash handling branches to them easily.
   desugar is not clever so will create redundant choices *)
let rec desugar t =
  match t with 
  | MessageG (msg, sender, receiver, t) -> ChoiceG (sender, MessageG (msg, sender, receiver, desugar t) :: [])
  | MuG (type_var, rec_vars, g) -> MuG (type_var, rec_vars, desugar g)
  | ChoiceG (name, ts) -> ChoiceG (name, List.map ts ~f:desugar)
  | CallG (caller, protocol, role_names, t) -> CallG (caller, protocol, role_names, desugar t)
  | e -> e

(* remove_redundant_choices removes any redundant choices created by desugar *)
let rec remove_redundant_choices t =
  match t with 
    | MessageG (msg, sender, receiver, t) -> MessageG (msg, sender, receiver, remove_redundant_choices t)
    | MuG (type_var, rec_vars, g) -> MuG (type_var, rec_vars, remove_redundant_choices g)
    | ChoiceG (_, []) -> EndG
    | ChoiceG (name, ts) -> ChoiceG (name, remove_choice name ts)
    | CallG (caller, protocol, participants, t) -> CallG (caller, protocol, participants, remove_redundant_choices t)
    | e -> e
  and remove_choice name ts =
    match ts with
      | [] -> []
      | (c :: cs) -> 
        match c with
          | ChoiceG(name, [t]) -> remove_redundant_choices t :: remove_choice name cs
          | _ -> remove_redundant_choices c :: remove_choice name cs

(* add_crash_branches passes through a global type, whenever it encounters a choice, it adds a new branch and places
   a single crash message in that branch *)
let rec add_crash_branches t =
    match t with
    | MessageG (msg, sender, receiver, t) -> MessageG (msg, sender, receiver, add_crash_branches t)
    | MuG (type_var, rec_vars, t) -> MuG (type_var, rec_vars, add_crash_branches t)
    | ChoiceG (name, t :: ts) -> 
      (match t with
        | MessageG (_, sender, receiver, _) -> 
          let crash_msg = MessageG ({label = LabelName.of_string "CRASH"; payload = []}, sender, receiver, EndG) in
            let other_branches = (List.map (t :: ts) ~f:add_crash_branches) in
              ChoiceG (name, other_branches @ [crash_msg])
        | e -> e)
    | CallG (caller, protocol, participants, t) -> CallG (caller, protocol, participants, add_crash_branches t)
    | e -> e

(* get_continuation is used when we have a particular choice branch, and we want to remove the first message from it 
   and return the rest *)
let get_continuation t = 
  match t with
    | MessageG (_, _, _, t) -> t
    | e -> e

(* add_continuation is used when we have a particular choice branch with only one message in it, and we want to append a
   continuation t' after that message *)
let add_continuation t t' = 
  match t with
    | MessageG (msg, sender, receiver, _) -> MessageG (msg, sender, receiver, t')
    | e -> e

(* make_tuple is self explanatory *)
let make_tuple e1 e2 = (e1, e2)

(* takes a list and returns all possible pair combinations of items in that list in the form of tuples *)
let rec all_pairings l = 
  match l with
    | [] -> []
    | [_] -> []
    | e :: es -> List.map es ~f:(make_tuple e) @ all_pairings es

(* get_makeshift_local_type takes a participant and a global type, and removes any messages in that global type that do not 
   involve the specified participant. so i guess you could say its essentially creating a local type for that participant, 
   but i describe it as "makeshift" because we dont change the actual programatical type from a global type *)
let rec get_makeshift_local_type p t =
  match t with
    | MessageG (msg, sender, receiver, t) -> 
      if roles_equal p sender || roles_equal p receiver then 
        MessageG(msg, sender, receiver, get_makeshift_local_type p t) 
      else
        get_makeshift_local_type p t
    | MuG (type_var, rec_vars, g) -> MuG (type_var, rec_vars, get_makeshift_local_type p g)
    | ChoiceG (name, ts) -> ChoiceG (name, List.map ts ~f:(get_makeshift_local_type p))
    | CallG (caller, protocol, participants, t) -> 
      if role_elem p participants then 
        CallG (caller, protocol, participants, get_makeshift_local_type p t) 
      else 
        get_makeshift_local_type p t
    | e -> e

(* get_type_def is used for when we find "continue X" and we want to get the definition for "rec X". it takes in
   the global protocol as a parameter to search for the definition *)
let rec get_type_def type_var t =
  match t with
    | MessageG (_, _, _, t) -> get_type_def type_var t
    | MuG (type_var, type_var_list, def) -> 
      if type_vars_equal type_var type_var then
        MuG (type_var, type_var_list, def)
      else
        get_type_def type_var def
    | ChoiceG (_, choices) -> get_type_def' type_var choices
    | _ -> EndG
  and get_type_def' type_var ts =
    match ts with
      | [] -> EndG
      | p :: ps -> 
        let check = get_type_def type_var p in
          match check with
            | EndG -> get_type_def' type_var ps
            | e -> e


(* sterilize will take a recursion function and remove any recurive calls from it. currently this function will remove
   any recursive call, i.e. if "continue Y" is found inside "rec X {}", it will still be removed, but this behaviour 
   can be changed very easily. *)
let rec sterilize type_def =
  match type_def with
    | MuG (type_var, _, g) -> sterilize' type_var g
    | _ -> failwith "sterilize failed: expected MuG" 
and sterilize' type_var t =
  match t with
    | MessageG (msg, sender, receiver, t) -> MessageG (msg, sender, receiver, sterilize' type_var t)
    | MuG (type_var, rec_vars, g) -> MuG (type_var, rec_vars, sterilize' type_var g)
    | TVarG (_, _, _) -> EndG
    | ChoiceG (name, ts) -> ChoiceG (name, List.map ts ~f:(sterilize' type_var))
    | CallG (caller, protocol, participants, t) -> CallG (caller, protocol, participants, sterilize' type_var t)
    | EndG -> EndG
    
    (* pair_mergeable_on returns true if two types are mergeable for a particular participant *)
    let rec pair_mergeable_on gp (t1, t2) p =
      (* tlt here is similar to gp, tlt is for top local type i.e. the full protocol *)
      let tlt = get_makeshift_local_type p gp in 
        let lt1 = get_makeshift_local_type p t1 in
          let lt2 = get_makeshift_local_type p t2 in
            match (lt1, lt2) with
              | MessageG (msg, sender, receiver, t), MessageG (msg', sender', receiver', t') ->
                  (if labels_equal msg msg' && roles_equal sender sender' && roles_equal receiver receiver' then
                      pair_mergeable_on gp (t, t') p
                    else if roles_equal sender sender' && roles_equal p receiver && roles_equal p receiver' then
                      true
                    else
                      false)
              | ChoiceG (_, ts), other | other, ChoiceG (_, ts) -> pair_mergeable_on' gp (other, ts) p
              | MuG (type_var, rec_vars, g), other | other, MuG (type_var, rec_vars, g) -> 
                pair_mergeable_on tlt (sterilize (MuG (type_var, rec_vars, g)), other) p
              | TVarG (type_var, _, _), other | other, TVarG (type_var, _, _) -> 
                pair_mergeable_on tlt (sterilize (get_type_def type_var tlt), other) p
              | EndG, EndG -> true
              | _ -> false
    
      (* pair_mergeable_on' is just a helper for merging with all the branches of a choice *)
      and pair_mergeable_on' gp (t, ts) p = 
        match ts with
          | [] -> failwith "pair_mergeable_on' failed: expected ChoiceG to have at least one branch"
          | [t'] -> pair_mergeable_on gp (t, t') p
          | t' :: ts' -> (pair_mergeable_on gp (t, t') p) && pair_mergeable_on' gp (t, ts') p

(* pair mergeable will determine whether a pair is mergeable for all participants. gp is the global
   protocol. we need carry around the full definition of the protocol for dealing with recursion *)
let pair_mergeable gp (t1, t2) =
  let participants = roles t1 in
    let participants' = roles t2 in
      if all_roles_equal participants participants' then 
        foldl (&&) true (List.map participants ~f:(pair_mergeable_on gp (t1, t2)))
      else 
        false

(* mergeable takes a protocol definition "gp" and a choice, and returns true iff the choice is mergeable. the
   protocol definition is needed to handle recursion *)
let mergeable gp choice = 
    match choice with
      | ChoiceG (_, ts) -> 
        let all_pairs = all_pairings ts in
          foldl (&&) true (List.map all_pairs ~f:(pair_mergeable gp))
      | _ -> failwith "mergeable failed: expected a ChoiceG"
    
(* let involved_with p gp = 
  match gp with
    | MessageG (_, _, _, t) -> 1 + msg_cnt t
    | MuG (_, _, t) -> msg_cnt t
    | TVarG (_, _, _) -> 0
    | ChoiceG (_, choices) -> biggest_msg_cnt choices
    | EndG -> 0
    | CallG (_, _, _, t) -> msg_cnt t *)


(* msg_cnt returns the number of messages in a global protocol *)
let rec msg_cnt t =
  match t with
    | MessageG (_, _, _, t) -> 1 + msg_cnt t
    | MuG (_, _, t) -> msg_cnt t
    | TVarG (_, _, _) -> 0
    | ChoiceG (_, choices) -> biggest_msg_cnt choices
    | EndG -> 0
    | CallG (_, _, _, t) -> msg_cnt t
and biggest_msg_cnt choices =
  match choices with
    | [] -> 0
    | [e] -> msg_cnt e
    | e :: es -> if msg_cnt e > biggest_msg_cnt es then 
                   msg_cnt e 
                 else 
                   biggest_msg_cnt es

(* get_shortest takes a list of branches (of a choice) and returns the shortest branch *)
let rec get_shortest_branch choices = 
  match choices with
    | [] -> failwith "get shortest failed: expected a non empty list"
    | [e] -> e
    | e :: e' :: es -> if msg_cnt e < msg_cnt e' then get_shortest_branch (e :: es) else get_shortest_branch (e' :: es)

    
(* add_shortest_branch_failure takes a global protocol and applies extend to every choice *)
let rec add_shortest_branch_failure gp =
  apply_to_every_choice (extend gp) gp
  (* extend takes a list of branches, determines which branch has the shortest continuation (by continuation i mean what 
    comes after the first message in the branch), and appends the shortest continuation to the crash message in the crash 
    branch *)
  and extend gp choice = 
    match choice with
      | ChoiceG (name, ts) -> if (mergeable gp choice) then choice else ChoiceG (name, extend' ts)
      | _ -> failwith "extend failed: expected ChoiceG"
  and extend' choices =
    let non_crash_branches = remove_last choices in
      let crash_branch = get_last choices in
        let shortest_choice_branch = get_shortest_branch (remove_last choices) in
          let shortest_choice_branch_continuation = get_continuation shortest_choice_branch in
            let complete_crash_branch = add_continuation crash_branch shortest_choice_branch_continuation in
              non_crash_branches @ complete_crash_branch :: []
          
(* add_local_graceful_failure takes in a protocol and outputs a protocol with local graceful failure *)  
let rec add_graceful_failure t =
  add_graceful_failure' t t
  and add_graceful_failure' gp t =
    let ps = roles t in
      apply_to_every_choice (extend gp ps) t
    and extend gp ps choice =
      match choice with
        | ChoiceG (name, ts) -> 
          let non_crash_branches = remove_last ts in
            let crash_branch = get_last ts in
              let relevant_participants = remove_participants (roles crash_branch) ps in
                let non_crash_branch = head non_crash_branches in
                  let crash_continuation = continuation gp crash_branch non_crash_branch relevant_participants [] in
                    let complete_crash_branch = append_continuation crash_branch crash_continuation in
                      ChoiceG (name, non_crash_branches @ complete_crash_branch :: [])
        | _ -> failwith "extend failed: expected ChoiceG"

  and continuation gp crash_branch non_crash_branch ps current_continuation =
    match non_crash_branch with
      | MessageG (msg, from_role, to_role, t) -> 
        if (role_elem from_role ps || role_elem to_role ps) then
          let ps = remove_participants (from_role :: to_role :: []) ps in
            let (cf, ct) = (crash_from crash_branch, crash_to crash_branch) in
              let addition = deal_with_msg (MessageG (msg, from_role, to_role, t)) cf ct current_continuation in
                let updated_continuation = current_continuation @ addition in
                  continuation gp crash_branch t ps updated_continuation
        else
          continuation gp crash_branch t ps current_continuation
      | MuG (_, _, t) -> continuation gp crash_branch t ps current_continuation
      | ChoiceG (_, choices) -> 
        (match choices with
          | [] -> []
          | e :: _ -> continuation gp crash_branch e ps current_continuation)
      | TVarG (type_var, _, _) -> continuation gp crash_branch (sterilize (get_type_def type_var gp)) ps current_continuation
      | _ -> current_continuation

  and deal_with_msg msg crash_from crash_to current_continuation =
    match msg with
      | MessageG (_, from_role, to_role, _) -> 
        if roles_equal from_role crash_from && roles_equal to_role crash_to
        || roles_equal from_role crash_to && roles_equal to_role crash_from
          then []
        else if roles_equal from_role crash_from
          then [MessageG ({label = LabelName.of_string "CRASH"; payload = []}, crash_from, to_role, EndG)]
        else if roles_equal from_role crash_to
          then [MessageG ({label = LabelName.of_string "EXIT"; payload = []}, crash_to, to_role, EndG)]
        else if (role_elem from_role (List.concat (List.map current_continuation ~f:roles)))  
          then [MessageG ({label = LabelName.of_string "EXIT"; payload = []}, from_role, to_role, EndG)]
        else failwith "deal_with_msg failed: cannot generate mergable crash branch"
      | _ -> failwith "deal_with_msg crashed: expected MessageG"

  and remove_participants to_remove participants = 
    match participants with
      | [] -> []
      | e :: es -> 
        if (role_elem e to_remove) then 
          remove_participants to_remove es 
        else 
          e :: remove_participants to_remove es

  and crash_from crash = 
    match crash with
      | MessageG (_, from_role, _, _) -> from_role
      | _ -> failwith "crash_from failed: expected a MessageG"

  and crash_to crash = 
    match crash with
      | MessageG (_, _, to_role, _) -> to_role
      | _ -> failwith "crash_to failed: expected a MessageG"

  and append_continuation crash_branch msgs =
    match crash_branch with
      | MessageG (msg, from_role, to_role, _) -> MessageG (msg, from_role, to_role, append_continuation' msgs)
      | _ -> failwith "append_continuation failed: expected a MessageG"

  and append_continuation' msgs =
    match msgs with
      | [] -> EndG
      | e :: es -> (match e with
                    | MessageG (msg, from_role, to_role, _) -> 
                      MessageG (msg, from_role, to_role, append_continuation' es)
                    | _ -> failwith "append_continuation failed: expected a MessageG")
         
(* add_local_graceful_failure takes in a protocol and outputs a protocol with local graceful failure *)
let rec add_local_graceful_failure t =
  add_local_graceful_failure' t t
  and add_local_graceful_failure' gp t =
    let ps = roles t in
      apply_to_every_choice (extend1 gp ps) t
  and extend1 gp ps choice = 
    match choice with
      | ChoiceG (name, ts) -> 
        let non_crash_branches = remove_last ts in
          let crash_branch = get_last ts in
            let relevant_participants = remove_participants (roles crash_branch) ps in
              let non_crash_branch = head non_crash_branches in
                let crash_continuation = continuation1 gp crash_branch non_crash_branch relevant_participants [] in
                  let complete_crash_branch = append_continuation crash_branch crash_continuation in
                    ChoiceG (name, non_crash_branches @ complete_crash_branch :: [])
      | _ -> failwith "extend failed: expected ChoiceG"
  and continuation1 gp crash_branch non_crash_branch ps current_continuation =
    match non_crash_branch with
      | MessageG (msg, from_role, to_role, t) -> 
        if (role_elem from_role ps || role_elem to_role ps) then
          let ps = remove_participants (from_role :: to_role :: []) ps in
            let (cf, ct) = (crash_from crash_branch, crash_to crash_branch) in
              let addition = deal_with_msg1 (MessageG (msg, from_role, to_role, t)) cf ct current_continuation in
                let updated_continuation = current_continuation @ addition in
                  continuation1 gp crash_branch t ps updated_continuation
        else
          continuation1 gp crash_branch t ps current_continuation
      | MuG (_, _, t) -> continuation1 gp crash_branch t ps current_continuation
      | ChoiceG (_, choices) -> 
        (match choices with
          | [] -> []
          | e :: _ -> continuation1 gp crash_branch e ps current_continuation)
      | TVarG (type_var, _, _) -> continuation gp crash_branch (sterilize (get_type_def type_var gp)) ps current_continuation
      | _ -> current_continuation
  and deal_with_msg1 msg crash_from crash_to current_continuation =
  match msg with
    | MessageG (_, from_role, to_role, _) -> 
      if roles_equal from_role crash_from && roles_equal to_role crash_to
      || roles_equal from_role crash_to && roles_equal to_role crash_from
        then []
      else if roles_equal from_role crash_from
        then [MessageG ({label = LabelName.of_string "CRASH"; payload = []}, crash_from, to_role, EndG)]
      else if roles_equal from_role crash_to
        then [MessageG ({label = LabelName.of_string "EXIT"; payload = []}, crash_to, to_role, EndG)]
      else if (role_elem from_role (List.concat (List.map current_continuation ~f:roles)))  
        then [MessageG ({label = LabelName.of_string "EXIT"; payload = []}, from_role, to_role, EndG)]
      else failwith "deal_with_msg failed: cannot generate mergable crash branch"
    | _ -> failwith "deal_with_msg1 crashed: expected MessageG"


(* remove_crash_branch simply drops the last (crash) branch from a choice *)
let rec remove_crash_branch t =
  match t with
  | ChoiceG (name, ts) -> (match ts with
                            | [] -> failwith "reomve_crash_branch failed: expected a choice with at least 2 branches"
                            | [_] -> failwith "reomve_crash_branch failed: expected a choice with at least 2 branches"
                            | e :: _ :: [] -> e
                            | es -> ChoiceG (name, remove_last es))
  | _ -> failwith "reomve_crash_branch failed: expected a ChoiceG"

(* trust_protocols will take a list of trusted protocols and remove any crash branches for choices on those participants *)
let rec trust_protocols trusted t = 
  match t with
    | MessageG (msg, sender, receiver, t) -> MessageG (msg, sender, receiver, trust_protocols trusted t)
    | MuG (type_var, rec_vars, g) -> MuG (type_var, rec_vars, trust_protocols trusted g)
    | ChoiceG (name, ts) -> 
      if (role_elem name trusted) then 
        remove_crash_branch (ChoiceG (name, (List.map ts ~f:(trust_protocols trusted)))) 
      else 
        ChoiceG (name, (List.map ts ~f:(trust_protocols trusted)))
    | CallG (caller, protocol, participants, t) -> CallG (caller, protocol, participants, trust_protocols trusted t)
    | e -> e

(* this function dispatches for each pattern to call all the relevant stages of generating the output *)
let apply_pattern pattern located_global_protocol =
  let begin_time = Unix.gettimeofday () in
    let gp = of_protocol located_global_protocol in
      let all_messages_as_choice = remove_redundant_choices (desugar gp) in
        let all_choices_with_crash = add_crash_branches all_messages_as_choice in
          let pattern_applied = pattern all_choices_with_crash in
            let result = trust_protocols [] pattern_applied in 
              let finish_time = Unix.gettimeofday () in
                Stdio.prerr_endline ("Run Time (s): " ^ (Float.to_string (finish_time -. begin_time))) ;
                  let file = "examples/crashPatternOutput.scr" in
                    let oc = Stdio.Out_channel.create file in
                      Stdio.Out_channel.output_string oc (show result) ; result 

(* shortest_branch_failure is the function used by nuscrlib to generate an earlier consideration for
   how to fail gracefully in which we simply copy the shortest alternative branch as the continuation in
   the crash branch. this will output to ther terminal as well as examples/crashPatternOutput.scr *)
let shortest_branch_failure located_global_protocol =
  apply_pattern add_shortest_branch_failure located_global_protocol

(* graceful_failure is the function used by nuscrlib to generate graceful failure for a protocol and 
   output it to the terminal as well as examples/crashPatternOutput.scr*)
let empty_crash_branch located_global_protocol =
  apply_pattern Fn.id located_global_protocol

(* graceful_failure is the function used by nuscrlib to generate graceful failure for a protocol and 
   output it to the terminal as well as examples/crashPatternOutput.scr*)
let graceful_failure located_global_protocol =
  apply_pattern add_graceful_failure located_global_protocol

(* graceful_failure is the function used by nuscrlib to generate graceful failure for a protocol and 
  output it to the terminal as well as examples/crashPatternOutput.scr*)
let local_graceful_failure located_global_protocol =
  apply_pattern add_local_graceful_failure located_global_protocol

  end
include CrashPattern

let rec flatten = function
  | ChoiceG (role, choices) ->
      let choices = List.map ~f:flatten choices in
      let lift = function
        | ChoiceG (role_, choices_) when RoleName.equal role role_ ->
            choices_
        | ChoiceG (role_, _choices) ->
            uerr (InconsistentNestedChoice (role, role_))
        | g -> [g]
      in
      ChoiceG (role, List.concat_map ~f:lift choices)
  | g -> g

let rec substitute g tvar g_sub =
  match g with
  | TVarG (tvar_, rec_exprs, _) when TypeVariableName.equal tvar tvar_ -> (
    match g_sub with
    | MuG (tvar__, rec_vars, g) ->
        let rec_vars =
          match
            List.map2
              ~f:(fun rec_var rec_expr ->
                {rec_var with rv_init_expr= rec_expr} )
              rec_vars rec_exprs
          with
          | Base.List.Or_unequal_lengths.Ok rec_vars -> rec_vars
          | _ -> unimpl ~here:[%here] "Error in substitution"
        in
        MuG (tvar__, rec_vars, g)
    | g_sub -> g_sub )
  | TVarG _ -> g
  | MuG (tvar_, _, _) when TypeVariableName.equal tvar tvar_ -> g
  | MuG (tvar_, rec_vars, g_) ->
      MuG (tvar_, rec_vars, substitute g_ tvar g_sub)
  | EndG -> EndG
  | MessageG (m, r1, r2, g_) -> MessageG (m, r1, r2, substitute g_ tvar g_sub)
  | ChoiceG (r, g_) ->
      ChoiceG (r, List.map ~f:(fun g__ -> substitute g__ tvar g_sub) g_)
  | CallG (caller, protocol, roles, g_) ->
      CallG (caller, protocol, roles, substitute g_ tvar g_sub)

let rec unfold = function
  | MuG (tvar, _, g_) as g -> substitute g_ tvar g
  | g -> g

let rec normalise = function
  | MessageG (m, r1, r2, g_) -> MessageG (m, r1, r2, normalise g_)
  | ChoiceG (r, g_) ->
      let g_ = List.map ~f:normalise g_ in
      flatten (ChoiceG (r, g_))
  | (EndG | TVarG _) as g -> g
  | MuG (tvar, rec_vars, g_) -> unfold (MuG (tvar, rec_vars, normalise g_))
  | CallG (caller, protocol, roles, g_) ->
      CallG (caller, protocol, roles, normalise g_)

let normalise_nested_t (nested_t : nested_t) =
  let normalise_protocol ~key ~data acc =
    let {gtype; _} = data in
    Map.add_exn acc ~key ~data:{data with gtype= normalise gtype}
  in
  Map.fold
    ~init:(Map.empty (module ProtocolName))
    ~f:normalise_protocol nested_t

let validate_refinements_exn t =
  let env =
    ( Expr.new_typing_env
    , Map.empty (module TypeVariableName)
    , Map.empty (module RoleName) )
  in
  let knowledge_add role_knowledge role variable =
    Map.update role_knowledge role ~f:(function
      | None -> Set.singleton (module VariableName) variable
      | Some s -> Set.add s variable )
  in
  let ensure_knowledge role_knowledge role e =
    let known_vars =
      Option.value
        ~default:(Set.empty (module VariableName))
        (Map.find role_knowledge role)
    in
    let free_vars = Expr.free_var e in
    let unknown_vars = Set.diff free_vars known_vars in
    if Set.is_empty unknown_vars then ()
    else uerr (UnknownVariableValue (role, Set.choose_exn unknown_vars))
  in
  let encode_progress_clause env payloads =
    let e =
      List.fold ~init:(Expr.Sexp.Atom "true")
        ~f:
          (fun e -> function
            | PValue (None, _) -> e
            | PValue (Some v, ty) ->
                let sort = Expr.smt_sort_of_type ty in
                let e =
                  match ty with
                  | Expr.PTRefined (v_, _, refinement) ->
                      if VariableName.equal v v_ then
                        Expr.Sexp.List
                          [ Expr.Sexp.Atom "and"
                          ; Expr.sexp_of_expr refinement
                          ; e ]
                      else
                        Err.violationf ~here:[%here]
                          "TODO: Handle the case where refinement and \
                           payload variables are different"
                  | _ -> e
                in
                Expr.Sexp.List
                  [ Expr.Sexp.Atom "exists"
                  ; Expr.Sexp.List
                      [ Expr.Sexp.List
                          [ Expr.Sexp.Atom (VariableName.user v)
                          ; Expr.Sexp.Atom sort ] ]
                  ; e ]
            | PDelegate _ -> (* Not supported *) e )
        payloads
    in
    let env =
      Expr.add_assert_s_expr (Expr.Sexp.List [Expr.Sexp.Atom "not"; e]) env
    in
    env
  in
  let ensure_progress env gs =
    let tyenv, _, _ = env in
    let encoded = Expr.encode_env tyenv in
    let rec gather_first_message = function
      | MessageG (m, _, _, _) -> [m.payload]
      | ChoiceG (_, gs) -> List.concat_map ~f:gather_first_message gs
      | MuG (_, _, g) -> gather_first_message g
      | TVarG (_, _, g) -> gather_first_message (Lazy.force g)
      | EndG -> []
      | CallG _ -> (* Not supported *) []
    in
    let first_messages = List.concat_map ~f:gather_first_message gs in
    let encoded =
      List.fold ~init:encoded ~f:encode_progress_clause first_messages
    in
    match Expr.check_sat encoded with
    | `Unsat -> ()
    | _ -> uerr StuckRefinement
  in
  let rec aux env =
    ( if Pragma.validate_refinement_satisfiability () then
      let tyenv, _, _ = env in
      Expr.ensure_satisfiable tyenv ) ;
    function
    | EndG -> ()
    | MessageG (m, role_send, role_recv, g) ->
        let payloads = m.payload in
        let f (tenv, rvenv, role_knowledge) = function
          | PValue (v_opt, p_type) ->
              if Expr.is_well_formed_type tenv p_type then
                match v_opt with
                | Some v ->
                    let tenv = Expr.env_append tenv v p_type in
                    let role_knowledge =
                      knowledge_add role_knowledge role_recv v
                    in
                    let role_knowledge =
                      knowledge_add role_knowledge role_send v
                    in
                    let () =
                      match p_type with
                      | Expr.PTRefined (_, _, e) ->
                          if Pragma.sender_validate_refinements () then
                            ensure_knowledge role_knowledge role_send e ;
                          if Pragma.receiver_validate_refinements () then
                            ensure_knowledge role_knowledge role_recv e
                      | _ -> ()
                    in
                    (tenv, rvenv, role_knowledge)
                | None -> (tenv, rvenv, role_knowledge)
              else uerr (IllFormedPayloadType (Expr.show_payload_type p_type))
          | PDelegate _ -> unimpl ~here:[%here] "Delegation as payload"
        in
        let env = List.fold ~init:env ~f payloads in
        aux env g
    | ChoiceG (_, gs) ->
        List.iter ~f:(aux env) gs ;
        if Pragma.validate_refinement_progress () then ensure_progress env gs
    | MuG (tvar, rec_vars, g) ->
        let f (tenv, rvenv, role_knowledge)
            {rv_name; rv_ty; rv_init_expr; rv_roles} =
          if Expr.is_well_formed_type tenv rv_ty then
            if Expr.check_type tenv rv_init_expr rv_ty then
              let tenv = Expr.env_append tenv rv_name rv_ty in
              let rvenv = Map.add_exn ~key:tvar ~data:rec_vars rvenv in
              let role_knowledge =
                List.fold ~init:role_knowledge
                  ~f:(fun acc role -> knowledge_add acc role rv_name)
                  rv_roles
              in
              (tenv, rvenv, role_knowledge)
            else
              uerr
                (TypeError
                   (Expr.show rv_init_expr, Expr.show_payload_type rv_ty) )
          else uerr (IllFormedPayloadType (Expr.show_payload_type rv_ty))
        in
        let env = List.fold ~init:env ~f rec_vars in
        aux env g
    | TVarG (tvar, rec_exprs, _) -> (
        let tenv, rvenv, role_knowledge = env in
        (* Unbound TypeVariable should not be possible, because it was
           previously validated *)
        let rec_vars = Option.value ~default:[] @@ Map.find rvenv tvar in
        match
          List.iter2
            ~f:(fun {rv_ty; rv_roles; _} rec_expr ->
              if Expr.check_type tenv rec_expr rv_ty then
                List.iter
                  ~f:(fun role ->
                    ensure_knowledge role_knowledge role rec_expr )
                  rv_roles
              else
                uerr
                  (TypeError
                     (Expr.show rec_expr, Expr.show_payload_type rv_ty) ) )
            rec_vars rec_exprs
        with
        | Base.List.Or_unequal_lengths.Ok () -> ()
        | Base.List.Or_unequal_lengths.Unequal_lengths ->
            unimpl ~here:[%here]
              "Error message for mismatched number of recursion variable \
               declaration and expressions" )
    | CallG _ -> assert false
  in
  aux env t

let add_missing_payload_field_names nested_t =
  let module Namegen = Namegen.Make (PayloadTypeName) in
  let add_missing_names namegen = function
    | PValue (None, n1) ->
        let payload_name_str =
          PayloadTypeName.of_string
            ("p_" ^ String.uncapitalize @@ Expr.show_payload_type n1)
        in
        let namegen, payload_name_str =
          Namegen.unique_name namegen payload_name_str
        in
        let payload_name =
          VariableName.of_other_name
            (module PayloadTypeName)
            payload_name_str
        in
        (namegen, PValue (Some payload_name, n1))
    | PValue (Some payload_name, n1) ->
        let payload_name_str =
          PayloadTypeName.create
            (String.uncapitalize @@ VariableName.user payload_name)
            (VariableName.where payload_name)
        in
        let namegen, payload_name_str =
          Namegen.unique_name namegen payload_name_str
        in
        let payload_name =
          VariableName.rename payload_name
            (PayloadTypeName.user payload_name_str)
        in
        (namegen, PValue (Some payload_name, n1))
    | PDelegate _ as p -> (namegen, p)
  in
  let rec add_missing_payload_names = function
    | MessageG (m, sender, recv, g) ->
        let g = add_missing_payload_names g in
        let {payload; _} = m in
        let namegen = Namegen.create () in
        let _, payload =
          List.fold_map payload ~init:namegen ~f:add_missing_names
        in
        MessageG ({m with payload}, sender, recv, g)
    | MuG (n, rec_vars, g) -> MuG (n, rec_vars, add_missing_payload_names g)
    | (TVarG _ | EndG) as p -> p
    | ChoiceG (r, gs) -> ChoiceG (r, List.map gs ~f:add_missing_payload_names)
    | CallG (caller, proto_name, roles, g) ->
        let g = add_missing_payload_names g in
        CallG (caller, proto_name, roles, g)
  in
  Map.map nested_t ~f:(fun ({gtype; _} as nested) ->
      {nested with gtype= add_missing_payload_names gtype} )

let nested_t_of_module (scr_module : Syntax.scr_module) =
  let open! Syntax in
  let scr_module = Extraction.rename_nested_protocols scr_module in
  let rec add_protocol protocols (protocol : global_protocol) =
    let nested_protocols = protocol.value.nested_protocols in
    let protocols =
      List.fold ~init:protocols ~f:add_protocol nested_protocols
    in
    let proto_name = protocol.value.name in
    let gtype = of_protocol protocol in
    let static_roles, dynamic_roles = protocol.value.split_roles in
    let nested_protocol_names =
      List.map ~f:(fun {Loc.value= {name; _}; _} -> name) nested_protocols
    in
    Map.add_exn protocols ~key:proto_name
      ~data:{static_roles; dynamic_roles; nested_protocol_names; gtype}
  in
  let all_protocols = scr_module.protocols @ scr_module.nested_protocols in
  let nested_t =
    List.fold
      ~init:(Map.empty (module ProtocolName))
      ~f:add_protocol all_protocols
  in
  normalise_nested_t @@ add_missing_payload_field_names nested_t
