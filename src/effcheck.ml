module Print = QCheck.Print
module Test = QCheck.Test
open Effast
open Effenv
open Effunif
open Effprint

(*
          (t:s) \in env
   ---------------------------- (VAR)
       env |- t : s/ff/ff

              (x:s), env |- m : t/ef/ev
   ----------------------------------------------------- (LAM)
     env |- (fun (x:s) -> m) : s -ef/ev-> t/ff/ff

      env |- f : s -ef/ev-> t/fef/fev     env |- x : s/xef/xev
    ------------------------------------------------------------ (APP)
       env |- f x : t/ef or fef or xef/(fef and xef) || fev

      env |- m : s/mef/mev     env, (x:s) |- n : t/nef/nev
    -------------------------------------------------------- (LET)
        env |- let x:s = m in n : t/mef or nef/mev or nev

 *)

(* First version, checks type-and-effect annotation *)
let tcheck_lit l =
  match l with
  | LitUnit -> (Unit, no_eff)
  | LitInt _ -> (Int, no_eff)
  | LitFloat _ -> (Float, no_eff)
  | LitBool _ -> (Bool, no_eff)
  | LitStr _ -> (String, no_eff)
;;

let check_option_invars typ name args =
  (* invariants:
    - typ must be Option _
    - name must be either "Some" or "None"
    - match name with
      | "Some" -> payload list must be a list of one element &&
        unwrapped type t of option must be same as (imm_type payload)
      | "None" -> payload list must be an empty list
      | _ -> "option adt name invariant failed"
   *)
  match typ with
  | Option t ->
    (match name with
    | "Some" ->
      (match args with
      | [ payload ] ->
        if types_compat (imm_type payload) t
        then Ok typ
        else Error "check_option_invars: some payload type invariant failed"
      | _ -> Error "check_option_invars: some payload arity failed")
    | "None" ->
      (match args with
      | [] -> Ok typ
      | _ -> Error "check_option_invars: none payload arity failed")
    | _ -> Error "check_option_invars: name invariant failed")
  | _ -> Error "check_option_invars: option type invariant failed"
;;

let check_tuple_invars typ arity args =
  (* check invar #1: arity i must be equal to length of args *)
  if not (List.length args = arity)
  then Error "tcheck: tuple arity invariant failed"
  else (
    (* check invar #2:
       [typ] must be [Tuple lst], where [lst] lists types that are same as types of args *)
    match typ with
    | Tuple t_lst ->
      if not (List.for_all2 (fun trm t -> types_compat (imm_type trm) t) args t_lst)
      then Error "tcheck: tuple argument type mismatch"
      else Ok typ
    | _ -> Error "tcheck: Constructor type and constr_descr mismatch")
;;

(** checks that a given pattern is well-typed, and returns the
   scrutinee type and well-typed environment returned by that pattern *)
let rec pcheck = function
  | PattVar (ty, x) -> VarMap.singleton x ty
  | PattConstr (ty, cstr, ps) ->
     let disjoint_union env1 env2 =
       VarMap.merge (fun x o1 o2 ->
           match o1, o2 with
             | None, None -> None
             | Some ty, None | None, Some ty -> Some ty
             | Some _, Some _ ->
                Test.fail_reportf
                  "pcheck: the variable %s occurs more than once" x)
       env1 env2 in
     let pcheck_args tys args =
       if List.length tys <> List.length args
       then Test.fail_report "pcheck: arity mismatch";
       List.fold_left2 (fun env ty p ->
           let p_ty = imm_pat_type p in
           if not (types_compat ty p_ty)
           (* Note: this check is in the opposite direction
              than the check on terms: in a constructedterm
              `K(e)`, the immediate type of `e` may be "less"
              (less effectful, less general) than the type expected by K;
              for patterns it is the converse, if the constructor
              K expects a sub-pattern at a given type, then the actual
              type of the sub-pattern cannot be less general (it would
              miss some possible scrutinees), it should be more general.

              For example if (x, y) claims to match on values of type
              ((a -{pure}-> b) * c), it is fine if the pattern variable x
              accepts the more general type (a -{impure}-> b) -- the typing
              environment will be populated with this less precise type.
              On the other hand, it would be unsound for (x, y) to claim to match
              on ((a -{impure}-> b) * c) and yet populate the environment with
              (x : (a -{pure}-> b)). *)
           then Test.fail_report "pcheck: inner pattern mismatch";
           disjoint_union env (pcheck p))
         VarMap.empty tys args
     in
     begin match cstr, ty with
       | TupleArity n, Tuple tys ->
          if not (List.length tys = n)
          then Test.fail_report "pcheck: tuple arity mismatch";
          pcheck_args tys ps
       | TupleArity _, _ ->
          Test.fail_report "pcheck: tuple constructor at non-tuple type";
       | Variant "None", Option _t ->
          pcheck_args [] ps
       | Variant "Some", Option t ->
          pcheck_args [t] ps
       | Variant (("Some" | "None") as cstr), _ ->
          Test.fail_reportf "pcheck: %s must have type option" cstr
       | Variant cstr, _ ->
          Test.fail_reportf "pcheck: unknown variant constructor %S" cstr
     end

(** checks that given term has indicated type and holds invariants associated with it *)
let rec tcheck env term =
  match term with
  | Lit l -> tcheck_lit l
  | Variable (t, v) ->
    (try
       let et = VarMap.find v env in
       if types_compat et t (* annotation may be more concrete then inferred type *)
       then (et, no_eff)
       else Test.fail_report "tcheck: variable types disagree"
     with Not_found -> Test.fail_report "tcheck: unknown variable")
  | ListTrm (typ, lst, eff) ->
    (match typ with
    | List elem_typ ->
      List.iter
        (fun e ->
          if not (types_compat (imm_type e) elem_typ)
          then Test.fail_report "tcheck: a list type mismatches its element's type")
        lst;
      (typ, eff)
    | _ -> Test.fail_report "tcheck: ListTrm must have a list type")
  (* typechecks variant constructors (currently checks only Option type but will be extended) *)
  | Constructor (typ, Variant name, args, eff) ->
    (match check_option_invars typ name args with
    | Ok _ -> (typ, eff)
    | Error e -> Test.fail_report e)
  (* typechecks tuple constructors *)
  | Constructor (typ, TupleArity i, args, eff) ->
    (match check_tuple_invars typ i args with
    | Ok _ -> (typ, eff)
    | Error e -> Test.fail_report e)
  | PatternMatch (ret_typ, matched_trm, cases, eff) ->
    tcheck env matched_trm |> ignore;
    let check_case (pat, body) =
      let body_env = VarMap.union (fun _ _ t -> Some t) env (pcheck pat) in
      let body_typ, body_eff = tcheck body_env body in
      if not (types_compat body_typ ret_typ && eff_leq body_eff eff)
      then Test.fail_report "tcheck: PatternMatch has a type mismatch";
    in
    List.iter check_case cases;
    (ret_typ, eff)
  | App (rt, m, at, n, ceff) ->
    let mtyp, meff = tcheck env m in
    let ntyp, neff = tcheck env n in
    (match mtyp with
    | Fun (_, e, _) ->
      if meff = no_eff || neff = no_eff
      then (
        match unify mtyp (Fun (at, ceff, rt)) with
        | Sol sub ->
          if types_compat (subst sub mtyp) (Fun (at, ceff, rt))
             (* we obtain annot by instantiating inferred type *)
          then (
            match unify ntyp at with
            | Sol sub' ->
              if types_compat (subst sub' ntyp) at
                 (* we obtain annot by instantiating inferred type *)
              then (
                let j_eff = eff_join e (eff_join meff neff) in
                if eff_leq j_eff ceff
                then (rt, j_eff)
                else
                  Test.fail_reportf
                    ("tcheck: effect annotation disagree in application:@;"
                    ^^ "@[<v>ceff is %a,@ j_eff is %a@]")
                    pp_eff
                    ceff
                    pp_eff
                    j_eff)
              else
                Test.fail_reportf
                  ("tcheck: argument types disagree in application:@;"
                  ^^ "@[<v>ntyp is %a,@ at is %a@]")
                  (pp_type ~effannot:true)
                  ntyp
                  (pp_type ~effannot:true)
                  at
            | No_sol ->
              Test.fail_reportf
                ("tcheck: argument types do not unify in application:@;"
                ^^ "@[<v>ntyp is %a,@ at is %a@]")
                (pp_type ~effannot:true)
                ntyp
                (pp_type ~effannot:true)
                at)
          else
            Test.fail_reportf
              ("tcheck: function types disagree in application:@;"
              ^^ "@[<v>sub is %a,@ mtyp is %a,@ (Fun (at,ceff,rt)) is %a@]")
              (pp_solution ~effannot:true)
              sub
              (pp_type ~effannot:true)
              mtyp
              (pp_type ~effannot:true)
              (Fun (at, ceff, rt))
        | No_sol ->
          Test.fail_reportf
            ("tcheck: function types do not unify in application:@;"
            ^^ "@[<v>mtyp is %a,@ (Fun (at,ceff,rt)) is %a@]")
            (pp_type ~effannot:true)
            mtyp
            (pp_type ~effannot:true)
            (Fun (at, ceff, rt)))
      else Test.fail_report "tcheck: application has subexprs with eff"
    | _ -> Test.fail_report "tcheck: application of non-function type")
  | Let (x, t, m, n, ltyp, leff) ->
    let mtyp, meff = tcheck env m in
    let ntyp, neff = tcheck (VarMap.add x mtyp env) n in
    if types_compat mtyp t (* annotation may be more concrete then inferred type *)
    then
      (*  annot "int list" instead of the more general "'a list" *)
      if types_compat ntyp ltyp
      then (
        let j_eff = eff_join meff neff in
        if eff_leq j_eff leff
        then (ntyp, leff)
        else
          Test.fail_reportf
            ("tcheck: let-effect disagrees with annotation:@;"
            ^^ "@[<v>leff is %a,@ j_eff is %a@]")
            pp_eff
            leff
            pp_eff
            j_eff)
      else
        Test.fail_reportf
          ("tcheck: let-body's type disagrees with annotation:@;"
          ^^ "@[<v>ntyp is %a, ltyp is %a@]")
          (pp_type ~effannot:true)
          ntyp
          (pp_type ~effannot:true)
          ltyp
    else Test.fail_report "tcheck: let-bound type disagrees with annotation"
  | Lambda (t, x, s, m) ->
    let mtyp, meff = tcheck (VarMap.add x s env) m in
    let ftyp = Fun (s, meff, mtyp) in
    if types_compat ftyp t
    then (ftyp, no_eff)
    else
      Test.fail_reportf
        ("tcheck: Lambda's type disagrees with annotation:@;"
        ^^ "@[<v>ftyp is %a,@ t is %a@]")
        (pp_type ~effannot:true)
        ftyp
        (pp_type ~effannot:true)
        t
  | If (t, b, m, n, e) ->
    let btyp, beff = tcheck env b in
    if btyp = Bool
    then
      if eff_leq beff e
      then (
        let mtyp, meff = tcheck env m in
        let ntyp, neff = tcheck env n in
        match unify mtyp ntyp with
        | Sol sub ->
          if types_compat (subst sub mtyp) t
             (* we obtain annot by instantiating inferred type *)
          then
            if types_compat (subst sub ntyp) t
               (* we obtain annot by instantiating inferred type *)
            then
              if eff_leq meff e && eff_leq neff e
              then (
                let e' = eff_join beff (eff_join meff neff) in
                (t, e'))
              else
                Test.fail_report "tcheck: If's branch effects disagree with annotation"
            else
              Test.fail_reportf
                ("tcheck: If's else branch type disagrees with annotation;@;"
                ^^ "@[<v>term is %a,@ ntyp is %a,@ (subst sub ntyp) is %a,@ t is %a@]")
                (pp_term ~typeannot:false)
                term
                (pp_type ~effannot:true)
                ntyp
                (pp_type ~effannot:true)
                (subst sub ntyp)
                (pp_type ~effannot:true)
                t
          else
            Test.fail_reportf
              ("tcheck: If's then branch type disagrees with annotation:@;"
              ^^ "@[<v>term is %a,@ mtyp is %a,@ (subst sub mtyp) is %a,@ t is %a@]")
              (pp_term ~typeannot:false)
              term
              (pp_type ~effannot:true)
              mtyp
              (pp_type ~effannot:true)
              (subst sub mtyp)
              (pp_type ~effannot:true)
              t
        | No_sol ->
          Test.fail_reportf
            ("tcheck: If's branch types do not unify:@;"
            ^^ "@[<v>term is %a,@ mtyp is %a,@ ntyp is %a@]")
            (pp_term ~typeannot:false)
            term
            (pp_type ~effannot:true)
            mtyp
            (pp_type ~effannot:true)
            ntyp)
      else Test.fail_report "tcheck: If's condition effect disagrees with annotation"
    else Test.fail_report "tcheck: If with non-Boolean condition"
;;
