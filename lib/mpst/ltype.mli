(** Local type management *)

(** This module defines local types and basic operations on them. *)
open! Base

open Names

(** Local types. See also {!LiteratureSyntax.local} for a simpler syntax. *)
type t =
  | RecvL of Gtype.message * RoleName.t * t
      (** [RecvL (msg, name, t)] waits for message [msg] from [name] and
          continues as [t] *)
  | SendL of Gtype.message * RoleName.t * t
      (** [SendL (msg, name, t)] sends message [msg] to [name] and continues
          as [t] *)
  | ChoiceL of RoleName.t * t list
      (** [ChoiceL (name, ts)] is a choice (internal or external) from [name]
          between the [ts] *)
  | TVarL of TypeVariableName.t * Expr.t list
      (** [TVarL (type_var, exprs)] is a type variable, scoped inside a
          recursion. [type_var] is the name of the type variable, [exprs] are
          expressions supplied into paramterised recursion, used in
          RefinementTypes extension. Otherwise an empty list is supplied when
          that feature is not used. *)
  | MuL of TypeVariableName.t * (bool (* Silent? *) * Gtype.rec_var) list * t
      (** [MuL (type_var, rec_vars, l)] is a recursive type, corresponding to
          the syntax `\mu t. L`, where t is represented by [type_var] and L
          is represented by [t]. [rec_vars] are recursion parameters, where
          the first component represents whether the variable is a silent
          variable (with multiplicity 0). These parameters are used in
          RefinementTypes extension for parameterised recursion, an empty
          list is supplied when that feature is not used. *)
  | EndL  (** Empty type *)
  | InviteCreateL of RoleName.t list * RoleName.t list * ProtocolName.t * t
      (** Send invitations to existing roles and set up/create dynamic
          pariticipants, used only in NestedProtocols extension *)
  | AcceptL of
      RoleName.t
      * ProtocolName.t
      * RoleName.t list
      * RoleName.t list
      * RoleName.t
      * t
      (** accept role\@Proto(roles...; new roles...) from X; t, used only in
          Nested Protocols extension *)
  | SilentL of VariableName.t * Expr.payload_type * t
      (** Used with refinement types to indicate knowledge obtained via a
          global protocol, used only in RefinementTypes extension *)

(** Unique id identifying a local protocol *)
module LocalProtocolId : sig
  type t [@@deriving show {with_path= false}, sexp_of]

  val create : ProtocolName.t -> RoleName.t -> t

  val get_role : t -> RoleName.t

  val get_protocol : t -> ProtocolName.t

  include Comparable.S with type t := t
end

(** Mapping of local protocol id to the protocol's roles and local type *)
type nested_t = (RoleName.t list * t) Map.M(LocalProtocolId).t

val show : t -> string
(** Converts a local type to a string. *)

val show_nested_t : nested_t -> string

val project : RoleName.t -> Gtype.t -> t
(** Project a global type into a particular role. *)

val project_nested_t : Gtype.nested_t -> nested_t
(** Generate the local protocols for a given global_t *)

val ensure_unique_tvars : nested_t -> nested_t
(** Ensure that all the local variables in each local protocol are globally
    unique, renaming variables to resolve conflicts *)

(** Mapping from local protocol ids to their unique local protocol names *)
type local_proto_name_lookup = LocalProtocolName.t Map.M(LocalProtocolId).t

val build_local_proto_name_lookup : nested_t -> local_proto_name_lookup
(** Builds a map containing the unique string representations for the unique
    local protocol ids *)

val show_lookup_table : local_proto_name_lookup -> string
(** Converts a local protocol name lookup table to a string *)

val lookup_local_protocol :
     local_proto_name_lookup
  -> ProtocolName.t
  -> RoleName.t
  -> LocalProtocolName.t
(** Return the unique local protocol name for a (role, protocol) pair *)

val lookup_protocol_id :
  local_proto_name_lookup -> LocalProtocolId.t -> LocalProtocolName.t
(** Look up the unique name for a local protocol id *)
