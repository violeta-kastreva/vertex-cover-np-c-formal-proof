open Univ
open Entries
open Names
open Pp
open Tm_util
open Quoted

(** The reifier to Coq values *)
module ConstrQuoted =
struct
  type t = Constr.t

  type quoted_ident = Constr.t (* of type Ast.ident *)
  type quoted_int = Constr.t (* of type nat *)
  type quoted_bool = Constr.t (* of type bool *)
  type quoted_name = Constr.t (* of type Ast.name *)
  type quoted_sort = Constr.t (* of type Ast.universe *)
  type quoted_cast_kind = Constr.t  (* of type Ast.cast_kind *)
  type quoted_kernel_name = Constr.t (* of type Ast.kername *)
  type quoted_inductive = Constr.t (* of type Ast.inductive *)
  type quoted_proj = Constr.t (* of type Ast.projection *)
  type quoted_global_reference = Constr.t (* of type Ast.global_reference *)

  type quoted_sort_family = Constr.t (* of type Ast.sort_family *)
  type quoted_constraint_type = Constr.t (* of type univ.constraint_type *)
  type quoted_univ_constraint = Constr.t (* of type univ.univ_constraint *)
  type quoted_univ_constraints = Constr.t (* of type univ.constraints *)
  type quoted_univ_instance = Constr.t (* of type univ.universe_instance *)
  type quoted_univ_context = Constr.t (* of type univ.universe_context *)
  type quoted_inductive_universes = Constr.t (* of type univ.universe_context *)

  type quoted_mind_params = Constr.t (* of type list (Ast.ident * list (ident * local_entry)local_entry) *)
  type quoted_ind_entry = quoted_ident * t * quoted_bool * quoted_ident list * t list
  type quoted_definition_entry = t * t option * quoted_univ_context
  type quoted_mind_entry = Constr.t (* of type Ast.mutual_inductive_entry *)
  type quoted_mind_finiteness = Constr.t (* of type Ast.mutual_inductive_entry ?? *)
  type quoted_entry = Constr.t (* of type option (constant_entry + mutual_inductive_entry) *)

  type quoted_context_decl = Constr.t (* in Ast *)
  type quoted_context = Constr.t (* in Ast *)

  type quoted_one_inductive_body = Constr.t (* of type Ast.one_inductive_body *)
  type quoted_mutual_inductive_body = Constr.t (* of type Ast.mutual_inductive_body *)
  type quoted_constant_body = Constr.t (* of type Ast.constant_body *)
  type quoted_global_decl = Constr.t (* of type Ast.global_decl *)
  type quoted_global_declarations = Constr.t (* of type Ast.global_declarations *)
  type quoted_program = Constr.t (* of type Ast.program *)

(*
  type quoted_reduction_strategy = Constr.t (* of type Ast.reductionStrategy *)
*)

  let resolve_symbol (path : string list) (tm : string) : Constr.t =
    gen_constant_in_modules contrib_name [path] tm

  let resolve_symbol_p (path : string list) (tm : string) : Globnames.global_reference =
    Coqlib.gen_reference_in_modules contrib_name [path] tm

  let pkg_datatypes = ["Coq";"Init";"Datatypes"]
  let pkg_string = ["Coq";"Strings";"String"]
  let pkg_base_reify = ["Template";"BasicAst"]
  let pkg_reify = ["Template";"Ast"]
  let pkg_template_monad = ["Template";"TemplateMonad"]
  let pkg_univ = ["Template";"Universes"]
  let pkg_level = ["Template";"Universes";"Level"]
  let pkg_variance = ["Template";"Universes";"Variance"]
  let pkg_ugraph = ["Template";"kernel";"uGraph"]
  let ext_pkg_univ s = List.append pkg_univ [s]

  let r_base_reify = resolve_symbol pkg_base_reify
  let r_reify = resolve_symbol pkg_reify
  let r_template_monad = resolve_symbol pkg_template_monad
  let r_template_monad_p = resolve_symbol_p pkg_template_monad

  let tString = resolve_symbol pkg_string "String"
  let tEmptyString = resolve_symbol pkg_string "EmptyString"
  let tO = resolve_symbol pkg_datatypes "O"
  let tS = resolve_symbol pkg_datatypes "S"
  let tnat = resolve_symbol pkg_datatypes "nat"
  let ttrue = resolve_symbol pkg_datatypes "true"
  let cSome = resolve_symbol pkg_datatypes "Some"
  let cNone = resolve_symbol pkg_datatypes "None"
  let tfalse = resolve_symbol pkg_datatypes "false"
  let unit_tt = resolve_symbol pkg_datatypes "tt"
  let tAscii = resolve_symbol ["Coq";"Strings";"Ascii"] "Ascii"
  let tlist = resolve_symbol pkg_datatypes "list"
  let c_nil = resolve_symbol pkg_datatypes "nil"
  let c_cons = resolve_symbol pkg_datatypes "cons"
  let prod_type = resolve_symbol pkg_datatypes "prod"
  let sum_type = resolve_symbol pkg_datatypes "sum"
  let option_type = resolve_symbol pkg_datatypes "option"
  let bool_type = resolve_symbol pkg_datatypes "bool"
  let cInl = resolve_symbol pkg_datatypes "inl"
  let cInr = resolve_symbol pkg_datatypes "inr"
  let prod a b = Constr.mkApp (prod_type, [| a ; b |])
  let c_pair = resolve_symbol pkg_datatypes "pair"
  let pair a b f s = Constr.mkApp (c_pair, [| a ; b ; f ; s |])

    (* reify the constructors in Template.Ast.v, which are the building blocks of reified terms *)
  let nAnon = r_base_reify "nAnon"
  let nNamed = r_base_reify "nNamed"
  let kVmCast = r_base_reify "VmCast"
  let kNative = r_base_reify "NativeCast"
  let kCast = r_base_reify "Cast"
  let kRevertCast = r_base_reify "RevertCast"
  let lProp = resolve_symbol pkg_level "lProp"
  let lSet = resolve_symbol pkg_level "lSet"
  let sfProp = r_base_reify "InProp"
  let sfSet = r_base_reify "InSet"
  let sfType = r_base_reify "InType"
  let tident = r_base_reify "ident"
  let tname = r_base_reify "name"
  let tIndTy = r_base_reify "inductive"
  let tmkInd = r_base_reify "mkInd"
  let tsort_family = r_base_reify "sort_family"
  let tmkdecl = r_reify "mkdecl"
  let (tTerm,tRel,tVar,tEvar,tSort,tCast,tProd,
       tLambda,tLetIn,tApp,tCase,tFix,tConstructor,tConst,tInd,tCoFix,tProj) =
    (r_reify "term", r_reify "tRel", r_reify "tVar", r_reify "tEvar",
     r_reify "tSort", r_reify "tCast", r_reify "tProd", r_reify "tLambda",
     r_reify "tLetIn", r_reify "tApp", r_reify "tCase", r_reify "tFix",
     r_reify "tConstruct", r_reify "tConst", r_reify "tInd", r_reify "tCoFix", r_reify "tProj")

  let tlevel = resolve_symbol pkg_level "t"
  let tLevel = resolve_symbol pkg_level "Level"
  let tLevelVar = resolve_symbol pkg_level "Var"
  let tunivLe = resolve_symbol (ext_pkg_univ "ConstraintType") "Le"
  let tunivLt = resolve_symbol (ext_pkg_univ "ConstraintType") "Lt"
  let tunivEq = resolve_symbol (ext_pkg_univ "ConstraintType") "Eq"
  let tmake_universe = resolve_symbol (ext_pkg_univ "Universe") "make''"

  (* let tunivcontext = resolve_symbol pkg_univ "universe_context" *)
  let tVariance = resolve_symbol pkg_variance "t"
  let cIrrelevant = resolve_symbol pkg_variance "Irrelevant"
  let cCovariant = resolve_symbol pkg_variance "Covariant"
  let cInvariant = resolve_symbol pkg_variance "Invariant"
  let cMonomorphic_ctx = resolve_symbol pkg_univ "Monomorphic_ctx"
  let cPolymorphic_ctx = resolve_symbol pkg_univ "Polymorphic_ctx"
  let cCumulative_ctx = resolve_symbol pkg_univ "Cumulative_ctx"
  let tUContext = resolve_symbol (ext_pkg_univ "UContext") "t"
  let tUContextmake = resolve_symbol (ext_pkg_univ "UContext") "make"
  (* let tConstraintSetempty = resolve_symbol (ext_pkg_univ "ConstraintSet") "empty" *)
  let tConstraintSetempty = Universes.constr_of_global (Coqlib.find_reference "template coq bug" (ext_pkg_univ "ConstraintSet") "empty")
  let tConstraintSetadd = Universes.constr_of_global (Coqlib.find_reference "template coq bug" (ext_pkg_univ "ConstraintSet") "add")
  let tmake_univ_constraint = resolve_symbol pkg_univ "make_univ_constraint"
  let tinit_graph = resolve_symbol pkg_ugraph "init_graph"
  let tadd_global_constraints = resolve_symbol pkg_ugraph  "add_global_constraints"

  let (tdef,tmkdef) = (r_base_reify "def", r_base_reify "mkdef")
  let (tLocalDef,tLocalAssum,tlocal_entry) = (r_reify "LocalDef", r_reify "LocalAssum", r_reify "local_entry")

  let (cFinite,cCoFinite,cBiFinite) = (r_reify "Finite", r_reify "CoFinite", r_reify "BiFinite")
  let tone_inductive_body = r_reify "one_inductive_body"
  let tBuild_one_inductive_body = r_reify "Build_one_inductive_body"
  let tBuild_mutual_inductive_body = r_reify "Build_mutual_inductive_body"
  let tBuild_constant_body = r_reify "Build_constant_body"
  let tglobal_decl = r_reify "global_decl"
  let tConstantDecl = r_reify "ConstantDecl"
  let tInductiveDecl = r_reify "InductiveDecl"
  let tglobal_declarations = r_reify "global_declarations"

  let tcontext_decl = r_reify "context_decl"
  let tcontext = r_reify "context"

  let tMutual_inductive_entry = r_reify "mutual_inductive_entry"
  let tOne_inductive_entry = r_reify "one_inductive_entry"
  let tBuild_mutual_inductive_entry = r_reify "Build_mutual_inductive_entry"
  let tBuild_one_inductive_entry = r_reify "Build_one_inductive_entry"
  let tConstant_entry = r_reify "constant_entry"
  let cParameterEntry = r_reify "ParameterEntry"
  let cDefinitionEntry = r_reify "DefinitionEntry"
  let cParameter_entry = r_reify "Build_parameter_entry"
  let cDefinition_entry = r_reify "Build_definition_entry"

  let (tcbv, tcbn, thnf, tall, tlazy, tunfold) = (r_template_monad "cbv", r_template_monad "cbn", r_template_monad "hnf", r_template_monad "all", r_template_monad "lazy", r_template_monad "unfold")

  let (tglobal_reference, tConstRef, tIndRef, tConstructRef) =
    (r_base_reify "global_reference", r_base_reify "ConstRef", r_base_reify "IndRef", r_base_reify "ConstructRef")

  let pkg_specif = ["Coq";"Init";"Specif"]
  let texistT = resolve_symbol pkg_specif "existT"
  let texistT_typed_term = r_template_monad_p "existT_typed_term"
                 
  let cMySome = resolve_symbol pkg_template_monad "mySome"
  let cMyNone = resolve_symbol pkg_template_monad "myNone"

  let unquote_sigt trm =
    let (h,args) = app_full trm [] in
    if Constr.equal h texistT then
      match args with
        _ :: _ :: x :: y :: [] -> (x, y)
      | _ -> bad_term_verb trm "unquote_sigt"
    else
      not_supported_verb trm "unquote_sigt"

  let unquote_pair trm =
    let (h,args) = app_full trm [] in
    if Constr.equal h c_pair then
      match args with
        _ :: _ :: x :: y :: [] -> (x, y)
      | _ -> bad_term_verb trm "unquote_pair"
    else
      not_supported_verb trm "unquote_pair"

  let rec unquote_list trm =
    let (h,args) = app_full trm [] in
    if Constr.equal h c_nil then
      []
    else if Constr.equal h c_cons then
      match args with
        _ :: x :: xs :: [] -> x :: unquote_list xs
      | _ -> bad_term_verb trm "unquote_list"
    else
      not_supported_verb trm "unquote_list"

  (* Unquote Coq nat to OCaml int *)
  let rec unquote_nat trm =
    let (h,args) = app_full trm [] in
    if Constr.equal h tO then
      0
    else if Constr.equal h tS then
      match args with
        n :: [] -> 1 + unquote_nat n
      | _ -> bad_term_verb trm "unquote_nat"
    else
      not_supported_verb trm "unquote_nat"

  let unquote_bool trm =
    if Constr.equal trm ttrue then
      true
    else if Constr.equal trm tfalse then
      false
    else not_supported_verb trm "from_bool"

  let unquote_char trm =
    let (h,args) = app_full trm [] in
    if Constr.equal h tAscii then
      match args with
        a :: b :: c :: d :: e :: f :: g :: h :: [] ->
        let bits = List.rev [a;b;c;d;e;f;g;h] in
        let v = List.fold_left (fun a n -> (a lsl 1) lor if unquote_bool n then 1 else 0) 0 bits in
        char_of_int v
      | _ -> bad_term_verb trm "unquote_char"
    else
      not_supported trm

  let unquote_string trm =
    let rec go n trm =
      let (h,args) = app_full trm [] in
      if Constr.equal h tEmptyString then
        Bytes.create n
      else if Constr.equal h tString then
        match args with
          c :: s :: [] ->
          let res = go (n + 1) s in
          let _ = Bytes.set res n (unquote_char c) in
          res
        | _ -> bad_term_verb trm "unquote_string"
      else
        not_supported_verb trm "unquote_string"
    in
    Bytes.to_string (go 0 trm)



  let to_coq_list typ =
    let the_nil = Constr.mkApp (c_nil, [| typ |]) in
    let rec to_list (ls : Constr.t list) : Constr.t =
      match ls with
	[] -> the_nil
      | l :: ls ->
	Constr.mkApp (c_cons, [| typ ; l ; to_list ls |])
    in to_list

  let quote_option ty = function
    | Some tm -> Constr.mkApp (cSome, [|ty; tm|])
    | None -> Constr.mkApp (cNone, [|ty|])

  (* Quote OCaml int to Coq nat *)
  let quote_int =
    (* the cache is global but only accessible through quote_int *)
    let cache = Hashtbl.create 10 in
    let rec recurse i =
      try Hashtbl.find cache i
      with
	Not_found ->
	  if i = 0 then
	    let result = tO in
	    let _ = Hashtbl.add cache i result in
	    result
	  else
	    let result = Constr.mkApp (tS, [| recurse (i - 1) |]) in
	    let _ = Hashtbl.add cache i result in
	    result
    in
    fun i ->
    if i >= 0 then recurse i else
      CErrors.anomaly Pp.(str "Negative int can't be unquoted to nat.")

  let quote_bool b =
    if b then ttrue else tfalse

  let quote_char i =
    Constr.mkApp (tAscii, Array.of_list (List.map (fun m -> quote_bool ((i land m) = m))
					 (List.rev [128;64;32;16;8;4;2;1])))

  let chars = Array.init 255 quote_char

  let quote_char c = chars.(int_of_char c)

  let string_hash = Hashtbl.create 420

  let to_string s =
    let len = String.length s in
    let rec go from acc =
      if from < 0 then acc
      else
        let term = Constr.mkApp (tString, [| quote_char (String.get s from) ; acc |]) in
        go (from - 1) term
    in
    go (len - 1) tEmptyString

  let quote_string s =
    try Hashtbl.find string_hash s
    with Not_found ->
      let term = to_string s in
      Hashtbl.add string_hash s term; term

  let quote_ident i =
    let s = Names.Id.to_string i in
    quote_string s

  let quote_name n =
    match n with
      Names.Name id -> Constr.mkApp (nNamed, [| quote_ident id |])
    | Names.Anonymous -> nAnon

  let quote_cast_kind k =
    match k with
      Constr.VMcast -> kVmCast
    | Constr.DEFAULTcast -> kCast
    | Constr.REVERTcast -> kRevertCast
    | Constr.NATIVEcast -> kNative

  let string_of_level s =
    to_string (Univ.Level.to_string s)

  let quote_level l =
    let open Univ in
    debug (fun () -> str"quote_level " ++ Level.pr l);
    if Level.is_prop l then lProp
    else if Level.is_set l then lSet
    else match Level.var_index l with
         | Some x -> Constr.mkApp (tLevelVar, [| quote_int x |])
         | None -> Constr.mkApp (tLevel, [| string_of_level l|])

  let quote_universe s =
    let levels = Universe.map (fun (l,i) -> pair tlevel bool_type (quote_level l) (if i > 0 then ttrue else tfalse)) s in
    to_coq_list (prod tlevel bool_type) levels

  (* todo : can be deduced from quote_level, hence shoud be in the Reify module *)
  let quote_univ_instance u =
    let arr = Univ.Instance.to_array u in
    to_coq_list tlevel (CArray.map_to_list quote_level arr)

  let quote_constraint_type (c : Univ.constraint_type) =
    match c with
    | Lt -> tunivLt
    | Le -> tunivLe
    | Eq -> tunivEq

  let quote_univ_constraint ((l1, ct, l2) : Univ.univ_constraint) =
    let l1 = quote_level l1 in
    let l2 = quote_level l2 in
    let ct = quote_constraint_type ct in
    Constr.mkApp (tmake_univ_constraint, [| l1; ct; l2 |])

  let quote_univ_constraints const =
    let const = Univ.Constraint.elements const in
    List.fold_left (fun tm c ->
        let c = quote_univ_constraint c in
        Constr.mkApp (tConstraintSetadd, [| c; tm|])
      ) tConstraintSetempty const

  let quote_variance v =
    match v with
    | Univ.Variance.Irrelevant -> cIrrelevant
    | Univ.Variance.Covariant -> cCovariant
    | Univ.Variance.Invariant -> cInvariant

  let quote_cuminfo_variance var =
    let var_list = CArray.map_to_list quote_variance var in
    to_coq_list tVariance var_list

  let quote_ucontext inst const =
    let inst' = quote_univ_instance inst in
    let const' = quote_univ_constraints const in
    Constr.mkApp (tUContextmake, [|inst'; const'|])

  let quote_univ_context uctx =
    let inst = Univ.UContext.instance uctx in
    let const = Univ.UContext.constraints uctx in
    Constr.mkApp (cMonomorphic_ctx, [| quote_ucontext inst const |])

  let quote_cumulative_univ_context cumi =
    let uctx = Univ.CumulativityInfo.univ_context cumi in
    let inst = Univ.UContext.instance uctx in
    let const = Univ.UContext.constraints uctx in
    let var = Univ.CumulativityInfo.variance cumi in
    let uctx' = quote_ucontext inst const in
    let var' = quote_cuminfo_variance var in
    let listvar = Constr.mkApp (tlist, [| tVariance |]) in
    let cumi' = pair tUContext listvar uctx' var' in
    Constr.mkApp (cCumulative_ctx, [| cumi' |])

  let quote_abstract_univ_context_aux uctx =
    let inst = Univ.UContext.instance uctx in
    let const = Univ.UContext.constraints uctx in
    Constr.mkApp (cPolymorphic_ctx, [| quote_ucontext inst const |])

  let quote_abstract_univ_context uctx =
    let uctx = Univ.AUContext.repr uctx in
    quote_abstract_univ_context_aux uctx

  let quote_inductive_universes uctx =
    match uctx with
    | Monomorphic_ind_entry uctx -> quote_univ_context (Univ.ContextSet.to_context uctx)
    | Polymorphic_ind_entry uctx -> quote_abstract_univ_context_aux uctx
    | Cumulative_ind_entry info ->
      quote_abstract_univ_context_aux (CumulativityInfo.univ_context info) (* FIXME lossy *)

  let quote_ugraph (g : UGraph.t) =
    let inst' = quote_univ_instance Univ.Instance.empty in
    let const' = quote_univ_constraints (UGraph.constraints_of_universes g) in
    let uctx = Constr.mkApp (tUContextmake, [|inst' ; const'|]) in
    Constr.mkApp (tadd_global_constraints, [|Constr.mkApp (cMonomorphic_ctx, [| uctx |]); tinit_graph|])

  let quote_sort s =
    quote_universe (Sorts.univ_of_sort s)

  let quote_sort_family = function
    | Sorts.InProp -> sfProp
    | Sorts.InSet -> sfSet
    | Sorts.InType -> sfType

  let quote_context_decl na b t =
    Constr.mkApp (tmkdecl, [| na; quote_option tTerm b; t |])

  let quote_context ctx =
    to_coq_list tcontext_decl ctx

  let mk_ctor_list =
    let ctor_list =
      let ctor_info_typ = prod (prod tident tTerm) tnat in
      to_coq_list ctor_info_typ
    in
    fun ls ->
    let ctors = List.map (fun (a,b,c) -> pair (prod tident tTerm) tnat
				              (pair tident tTerm a b) c) ls in
    ctor_list ctors

  let mk_proj_list d =
    to_coq_list (prod tident tTerm)
                (List.map (fun (a, b) -> pair tident tTerm a b) d)

  let quote_inductive (kn, i) =
    Constr.mkApp (tmkInd, [| kn; i |])

  let rec seq f t =
    if f < t then f :: seq (f + 1) t
    else []

  let quote_proj ind pars args =
    pair (prod tIndTy tnat) tnat (pair tIndTy tnat ind pars) args

  let mkAnon = nAnon
  let mkName id = Constr.mkApp (nNamed, [| id |])
  let quote_kn kn = quote_string (KerName.to_string kn)

  let mkRel i = Constr.mkApp (tRel, [| i |])
  let mkVar id = Constr.mkApp (tVar, [| id |])
  let mkEvar n args = Constr.mkApp (tEvar, [| n; to_coq_list tTerm (Array.to_list args) |])
  let mkSort s = Constr.mkApp (tSort, [| s |])
  let mkCast c k t = Constr.mkApp (tCast, [| c ; k ; t |])
  let mkConst kn u = Constr.mkApp (tConst, [| kn ; u |])
  let mkProd na t b =
    Constr.mkApp (tProd, [| na ; t ; b |])
  let mkLambda na t b =
    Constr.mkApp (tLambda, [| na ; t ; b |])
  let mkApp f xs =
    Constr.mkApp (tApp, [| f ; to_coq_list tTerm (Array.to_list xs) |])

  let mkLetIn na t t' b =
    Constr.mkApp (tLetIn, [| na ; t ; t' ; b |])

  let mkFix ((a,b),(ns,ts,ds)) =
    let mk_fun xs i =
      Constr.mkApp (tmkdef, [| tTerm ; Array.get ns i ;
                             Array.get ts i ; Array.get ds i ; Array.get a i |]) :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length a)) in
    let block = to_coq_list (Constr.mkApp (tdef, [| tTerm |])) (List.rev defs) in
    Constr.mkApp (tFix, [| block ; b |])

  let mkConstruct (ind, i) u =
    Constr.mkApp (tConstructor, [| ind ; i ; u |])

  let mkCoFix (a,(ns,ts,ds)) =
    let mk_fun xs i =
      Constr.mkApp (tmkdef, [| tTerm ; Array.get ns i ;
                             Array.get ts i ; Array.get ds i ; tO |]) :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length ns)) in
    let block = to_coq_list (Constr.mkApp (tdef, [| tTerm |])) (List.rev defs) in
    Constr.mkApp (tCoFix, [| block ; a |])

  let mkInd i u = Constr.mkApp (tInd, [| i ; u |])

  let mkCase (ind, npar) nargs p c brs =
    let info = pair tIndTy tnat ind npar in
    let branches = List.map2 (fun br nargs ->  pair tnat tTerm nargs br) brs nargs in
    let tl = prod tnat tTerm in
    Constr.mkApp (tCase, [| info ; p ; c ; to_coq_list tl branches |])

  let mkProj kn t =
    Constr.mkApp (tProj, [| kn; t |])

  let mk_one_inductive_body (a, b, c, d, e) =
    let c = to_coq_list tsort_family c in
    let d = mk_ctor_list d in
    let e = mk_proj_list e in
    Constr.mkApp (tBuild_one_inductive_body, [| a; b; c; d; e |])

  let mk_mutual_inductive_body npars params inds uctx =
    let inds = to_coq_list tone_inductive_body inds in
    Constr.mkApp (tBuild_mutual_inductive_body, [|npars; params; inds; uctx|])

  let mk_constant_body ty tm uctx =
    let tm = quote_option tTerm tm in
    Constr.mkApp (tBuild_constant_body, [|ty; tm; uctx|])

  let mk_inductive_decl kn mind =
    Constr.mkApp (tInductiveDecl, [|kn; mind|])

  let mk_constant_decl kn bdy =
    Constr.mkApp (tConstantDecl, [|kn; bdy|])

  let empty_global_declartions =
    Constr.mkApp (c_nil, [| tglobal_decl |])

  let add_global_decl d l =
    Constr.mkApp (c_cons, [|tglobal_decl; d; l|])

  let mk_program = pair tglobal_declarations tTerm

  let quote_mind_finiteness (f: Declarations.recursivity_kind) =
    match f with
    | Declarations.Finite -> cFinite
    | Declarations.CoFinite -> cCoFinite
    | Declarations.BiFinite -> cBiFinite

  let make_one_inductive_entry (iname, arity, templatePoly, consnames, constypes) =
    let consnames = to_coq_list tident consnames in
    let constypes = to_coq_list tTerm constypes in
    Constr.mkApp (tBuild_one_inductive_entry, [| iname; arity; templatePoly; consnames; constypes |])

  let quote_mind_params l =
    let pair i l = pair tident tlocal_entry i l in
    let map (id, ob) =
      match ob with
      | Left b -> pair id (Constr.mkApp (tLocalDef,[|b|]))
      | Right t -> pair id (Constr.mkApp (tLocalAssum,[|t|]))
    in
    let the_prod = Constr.mkApp (prod_type,[|tident; tlocal_entry|]) in
    to_coq_list the_prod (List.map map l)

  let quote_mutual_inductive_entry (mf, mp, is, mpol) =
    let is = to_coq_list tOne_inductive_entry (List.map make_one_inductive_entry is) in
    let mpr = Constr.mkApp (cNone, [|bool_type|]) in
    let mr = Constr.mkApp (cNone, [|Constr.mkApp (option_type, [|tident|])|])  in
    Constr.mkApp (tBuild_mutual_inductive_entry, [| mr; mf; mp; is; mpol; mpr |])


  let quote_constant_entry (ty, body, ctx) =
    match body with
    | None ->
      Constr.mkApp (cParameterEntry, [| Constr.mkApp (cParameter_entry, [|ty; ctx|]) |])
    | Some body ->
      Constr.mkApp (cDefinitionEntry,
                  [| Constr.mkApp (cDefinition_entry, [|ty;body;ctx;tfalse (*FIXME*)|]) |])

  let quote_entry decl =
    let opType = Constr.mkApp(sum_type, [|tConstant_entry;tMutual_inductive_entry|]) in
    let mkSome c t = Constr.mkApp (cSome, [|opType; Constr.mkApp (c, [|tConstant_entry;tMutual_inductive_entry; t|] )|]) in
    let mkSomeDef = mkSome cInl in
    let mkSomeInd  = mkSome cInr in
    match decl with
    | Some (Left centry) -> mkSomeDef (quote_constant_entry centry)
    | Some (Right mind) -> mkSomeInd mind
    | None -> Constr.mkApp (cNone, [| opType |])


  let quote_global_reference : Globnames.global_reference -> quoted_global_reference = function
    | Globnames.VarRef _ -> CErrors.user_err (str "VarRef unsupported")
    | Globnames.ConstRef c ->
       let kn = quote_kn (Names.Constant.canonical c) in
       Constr.mkApp (tConstRef, [|kn|])
    | Globnames.IndRef (i, n) ->
       let kn = quote_kn (Names.MutInd.canonical i) in
       let n = quote_int n in
       Constr.mkApp (tIndRef, [|quote_inductive (kn ,n)|])
    | Globnames.ConstructRef ((i, n), k) ->
       let kn = quote_kn (Names.MutInd.canonical i) in
       let n = quote_int n in
       let k = (quote_int (k - 1)) in
       Constr.mkApp (tConstructRef, [|quote_inductive (kn ,n); k|])

end
