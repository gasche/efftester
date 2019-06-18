(* *************************************************************** *)
(* OCaml compiler backend tester                                   *)
(* Initial version by Patrick Kasting and Mathias Nygaard Justesen *)
(* Type and effect extension by Jan Midtgaard                      *)
(* *************************************************************** *)

open QCheck

(** Compilation *)

(* Write OCaml source to file *)
let write_prog src filename =
  let ostr = open_out filename in
  let () = output_string ostr src in
  close_out ostr
;;

let run srcfile compil_filename compil_comm =
  let exefile = "generated_tests/" ^ compil_filename in
  let exitcode = Sys.command (compil_comm ^ " " ^ srcfile ^ " -o " ^ exefile) in
  (* Check that compilation was successful *)
  if exitcode <> 0
  then
    failwith
      (compil_filename ^ " compilation failed with error code " ^ string_of_int exitcode)
  else (
    (* Run the compiled program *)
    let runcode = Sys.command ("./" ^ exefile ^ " >" ^ exefile ^ ".out 2>&1") in
    (runcode, exefile ^ ".out"))
;;

let is_native_byte_equiv (*printFunction*) src =
  (* Write OCaml source to file *)
  let file = "generated_tests/test.ml" in
  let () = write_prog src file in
  let ncode, nout = run file "native" "ocamlopt -O3 -w -5-26" in
  (* -w -5@20-26 *)
  (* Silence warnings for partial applications and unused variables *)
  let bcode, bout = run file "byte" "ocamlc -w -5-26" in
  let comp = Sys.command ("diff -q " ^ nout ^ " " ^ bout ^ " > /dev/null") in
  ncode = bcode && comp = 0
;;

(** AST type definitions  *)

type variable = string
type eff = bool * bool
type typevar = int

let resettypevar, newtypevar =
  let count = ref 0 in
  ( (fun () -> count := 0),
    fun () ->
      let old = !count in
      incr count;
      old )
;;

let resetvar, newvar =
  let count = ref 0 in
  ( (fun () -> count := 0),
    fun () ->
      let old = !count in
      incr count;
      "var" ^ string_of_int old )
;;

let reseteffvar, neweffvar =
  let count = ref 0 in
  ( (fun () -> count := 0),
    fun () ->
      let old = !count in
      incr count;
      "eff" ^ string_of_int old )
;;

type etype =
  | Typevar of typevar
  | Unit
  | Int
  | Float
  | Bool
  | String
  | List of etype
  | Fun of etype * eff * etype

let rec ftv = function
  | Typevar a -> [ a ]
  | Unit | Int | Float | Bool | String -> []
  | List et -> ftv et
  | Fun (a, _, r) -> ftv a @ ftv r
;;

type lit =
  | LitUnit
  | LitInt of int
  | LitFloat of float
  | LitBool of bool
  | LitStr of string
  | LitList of lit list

type term =
  | Lit of lit
  | Variable of etype * variable
  | Lambda of etype * variable * etype * term
  | App of etype * term * etype * term * eff
  | Let of variable * etype * term * term * etype * eff
  | If of etype * term * term * term * eff

(** Printing functions  *)

let rec type_to_ocaml ?(effannot = false) sb = function
  | Typevar a -> Printf.bprintf sb "'a%d" a
  | Unit -> Printf.bprintf sb "unit"
  | Int -> Printf.bprintf sb "int"
  | Float -> Printf.bprintf sb "float"
  | Bool -> Printf.bprintf sb "bool"
  | String -> Printf.bprintf sb "string"
  | List s -> Printf.bprintf sb "(%a) list" (type_to_ocaml ~effannot) s
  | Fun (s, e, t) ->
    let print_simple_type sb s =
      match s with
      | Unit | Int | Float | Bool | String | List _ | Typevar _ ->
        Printf.bprintf sb "%a" (type_to_ocaml ~effannot) s
      | Fun _ -> Printf.bprintf sb "(%a)" (type_to_ocaml ~effannot) s
    in
    let print_effannot sb = function
      | None -> ()
      | Some (ef, ev) -> Printf.bprintf sb "%B/%B" ef ev
    in
    let print_type sb t = Printf.bprintf sb "%a" (type_to_ocaml ~effannot) t in
    Printf.bprintf
      sb
      "%a -%a> %a"
      print_simple_type
      s
      print_effannot
      (if effannot then Some e else None)
      print_type
      t
;;

let type_to_str ?(effannot = false) typ =
  let sb = Buffer.create 20 in
  let () = type_to_ocaml ~effannot sb typ in
  Buffer.contents sb
;;

let eff_to_str ((ef, ev) : eff) = Printf.sprintf "(%B,%B)" ef ev

(* BNF grammar:

    exp ::= l | x | fun (x:t) -> exp | exp exp | let (x:t) = exp in exp

   Same language but unambiguously formulated grammar:

    exp ::= app | fun (x:t) -> exp | let (x:t) = exp in exp | if exp then exp else exp
    app ::= arg | app arg
    arg ::= l | x | (exp)

   The following prettyprinter is structured according to this grammar to cut down on
   the needless parentheses
*)
let term_to_ocaml ?(typeannot = true) term =
  let rec lit_to_ocaml_sb sb = function
    | LitUnit -> Printf.bprintf sb "()"
    | LitInt i -> if i < 0 then Printf.bprintf sb "(%d)" i else Printf.bprintf sb "%d" i
    | LitFloat f ->
      if f <= 0. then Printf.bprintf sb "(%F)" f else Printf.bprintf sb "%F" f
    (* We want parentheses when f equals (-0.);
        Without parentheses -0. is interpreted as an arithmetic operation function. *)
    | LitBool b -> Printf.bprintf sb "%B" b
    | LitStr s -> Printf.bprintf sb "%S" s
    | LitList ls ->
      let print_lst sb ls =
        List.iter (fun elt -> Printf.bprintf sb "%a; " lit_to_ocaml_sb elt) ls
      in
      Printf.bprintf sb "[%a]" print_lst ls
  in
  let rec exp sb t =
    let type_to_ocaml_noannot = type_to_ocaml ~effannot:false in
    let print_binder sb (x, t) =
      if typeannot
      then Printf.bprintf sb "(%s: %a)" x type_to_ocaml_noannot t
      else Printf.bprintf sb "%s" x
    in
    match t with
    | Lambda (_, x, t, m) -> Printf.bprintf sb "fun %a -> %a" print_binder (x, t) exp m
    | Let (x, t, m, n, _, _) ->
      Printf.bprintf sb "let %a = %a in %a" print_binder (x, t) exp m exp n
    | If (_, b, m, n, _) -> Printf.bprintf sb "if %a then %a else %a" exp b exp m exp n
    | _ -> app sb t
  and app sb t =
    match t with
    | App (_, m, _, n, _) -> Printf.bprintf sb "%a %a" app m arg n
    | _ -> arg sb t
  and arg sb t =
    match t with
    | Lit l -> lit_to_ocaml_sb sb l
    | Variable (_, s) -> Printf.bprintf sb "%s" s
    | _ -> Printf.bprintf sb "(%a)" exp t
  in
  let sb = Buffer.create 80 in
  let () = exp sb term in
  Buffer.contents sb
;;

(** Effect system function *)

let no_eff = (false, false)
let eff_join (ef, ev) (ef', ev') = (ef || ef', ev || ev')

let eff_leq eff eff_exp =
  match (eff, eff_exp) with
  | (false, true), _ | _, (false, true) -> failwith "eff_leq: this should not happen"
  | (false, false), _ -> true (* no eff, compat with anything *)
  | (true, false), (true, _) -> true
  | (true, true), (true, true) -> true
  | _, _ -> false
;;

let rec occurs tvar = function
  | Typevar a -> tvar = a
  | List a -> occurs tvar a
  | Fun (a, _, b) -> occurs tvar a || occurs tvar b
  | _ -> false
;;

let rec arity = function
  | Fun (_, _, b) -> 1 + arity b
  | _ -> 0
;;

let rec subst repl t =
  match t with
  | Unit | Int | Float | Bool | String -> t
  | Typevar a -> (try List.assoc a repl with Not_found -> t)
  | Fun (l, e, r) -> Fun (subst repl l, e, subst repl r)
  | List u -> List (subst repl u)
;;

type unify_solution =
  | No_sol
  | Sol of (typevar * etype) list

exception No_solution

let rec unify_list = function
  | [] -> []
  | (l, r) :: rest ->
    let sub = unify_list rest in
    (match (subst sub l, subst sub r) with
    | Unit, Unit -> sub
    | Int, Int -> sub
    | Float, Float -> sub
    | Bool, Bool -> sub
    | String, String -> sub
    | Typevar a, Typevar b -> if a = b then sub else (a, r) :: sub
    | List a, List b ->
      let sub' = unify_list [ (a, b) ] in
      sub' @ sub
    | Fun (a, _, b), Fun (c, _, d) ->
      let sub' = unify_list [ (a, c); (b, d) ] in
      sub' @ sub
    | Typevar a, _ -> if occurs a r then raise No_solution else (a, r) :: sub
    | _, Typevar a -> if occurs a l then raise No_solution else (a, l) :: sub
    | Unit, _ | Int, _ | Float, _ | Bool, _ | String, _ | List _, _ | Fun _, _ ->
      raise No_solution)
;;

let unify r t = try Sol (unify_list [ (r, t) ]) with No_solution -> No_sol

(* determines whether the first arg is a generalization of the second *)
(* or framed differently: whether the second is a particular instance of the first *)
let rec types_compat t t' =
  match (t, t') with
  | Unit, Unit -> true
  | Unit, _ -> false
  | Int, Int -> true
  | Int, _ -> false
  | Float, Float -> true
  | Float, _ -> false
  | Bool, Bool -> true
  | Bool, _ -> false
  | String, String -> true
  | String, _ -> false
  | Fun (at, e, rt), Fun (at', e', rt') ->
    types_compat at' at && types_compat rt rt' && eff_leq e e'
  | Fun _, _ -> false
  | List et, List et' -> types_compat et et'
  | List _, _ -> false
  | Typevar _, _ ->
    (match unify t t' with
    | No_sol -> false
    | Sol _ -> true)
;;

let imm_eff t =
  match t with
  | Lit _ | Variable (_, _) | Lambda (_, _, _, _) -> no_eff
  | App (_, _, _, _, e) -> e
  | Let (_, _, _, _, _, e) -> e
  | If (_, _, _, _, e) -> e
;;

let imm_type t =
  let rec lit_type l =
    match l with
    | LitUnit -> Unit
    | LitInt _ -> Int
    | LitFloat _ -> Float
    | LitBool _ -> Bool
    | LitStr _ -> String
    | LitList l ->
      let etyp =
        List.fold_left
          (fun typacc elem ->
            let etyp = lit_type elem in
            if types_compat typacc etyp (* if typacc is a generalization of etyp *)
            then etyp
            else if types_compat etyp typacc (* if etyp is a generalization of typeacc *)
            then typacc
            else
              failwith
                ("lit_type: elements in list literal disagree"
                ^ "  typacc is "
                ^ type_to_str ~effannot:true typacc
                ^ "  etyp is "
                ^ type_to_str ~effannot:true etyp))
          (Typevar (newtypevar ()))
          l
      in
      List etyp
  in
  match t with
  | Lit l -> lit_type l
  | Variable (typ, _) -> typ
  | Lambda (typ, _, _, _) -> typ
  | App (typ, _, _, _, _) -> typ
  | Let (_, _, _, _, typ, _) -> typ
  | If (typ, _, _, _, _) -> typ
;;

(** Environment type definitions and functions *)

module TypeSet = Set.Make (struct
  type t = etype

  let compare = Pervasives.compare
end)

module VarSet = Set.Make (struct
  type t = variable

  let compare = String.compare
end)

module VarMap = Map.Make (struct
  type t = variable

  let compare = String.compare
end)

module TypeMap = Map.Make (struct
  type t = etype

  let compare = Pervasives.compare
end)

let rec normalize_eff t =
  match t with
  | Typevar _ | Unit | Int | Float | Bool | String -> t
  | List t' ->
    let t'' = normalize_eff t' in
    List t''
  | Fun (s, _, t) -> Fun (normalize_eff s, no_eff, normalize_eff t)
;;

let add_multi_map key value map =
  (* assume key has been normalized *)
  match TypeMap.find key map with
  | exception Not_found -> TypeMap.add key (VarSet.singleton value) map
  | s ->
    let new_set = VarSet.add value s in
    TypeMap.add key new_set map
;;

let remove_multi_map key value map =
  (* assume key has been normalized *)
  let old_key_set = TypeMap.find key map in
  let fixed_old_type_set = VarSet.remove value old_key_set in
  if VarSet.is_empty fixed_old_type_set
  then TypeMap.remove key map
  else TypeMap.add key fixed_old_type_set map
;;

(** maps a variable to its type *)
type type_env = etype VarMap.t

(** maps a type to a set of variables with that type *)
type binding_env = VarSet.t TypeMap.t

(** Includes three elements:
  env (Gamma) : maps variables to types
  rev_env : maps types to sets of variables
  ret_env : maps return types to sets of variables
*)
type tridir_env = type_env * binding_env * binding_env

let rec get_return_types = function
  | Fun (s, e, t) -> Fun (s, e, t) :: get_return_types t
  | t -> [ t ]
;;

(* special entry Typevar (-1) holds all vars with polymorphic return type *)
let polyentry = Typevar (-1)

let add_var var new_type (env, rev_env, ret_env) =
  let env' = VarMap.add var new_type env in
  (* Overrides existing entry *)
  let norm_new_type = normalize_eff new_type in
  let old_type = try Some (VarMap.find var env) with Not_found -> None in
  let rev_env' =
    let fixed_rev_env =
      match old_type with
      | Some old_type -> remove_multi_map (normalize_eff old_type) var rev_env
      | None -> rev_env
    in
    add_multi_map norm_new_type var fixed_rev_env
  in
  let ret_env' =
    let rts = get_return_types norm_new_type in
    let fixed_ret_env =
      match old_type with
      | None -> ret_env
      | Some s ->
        List.fold_left
          (fun r_env rt ->
            if ftv rt = []
               (* return type polymorphic? Then syntactic comp. will not find it *)
            then remove_multi_map rt var r_env
            else remove_multi_map polyentry var r_env)
          ret_env
          (get_return_types (normalize_eff s))
    in
    List.fold_left
      (fun r_env rt ->
        if ftv rt = []
           (* return type polymorphic? Then syntactic comp. will not find it *)
        then add_multi_map rt var r_env
        else add_multi_map polyentry var r_env)
      fixed_ret_env
      rts
  in
  (env', rev_env', ret_env')
;;

let lookup_var x (env, _, _) = try Some (VarMap.find x env) with Not_found -> None

let lookup_type s (_, rev_env, _) =
  try TypeMap.find s rev_env with Not_found -> VarSet.empty
;;

let lookup_return s (env, _, ret_env) =
  let concrete_set = try TypeMap.find s ret_env with Not_found -> VarSet.empty in
  let arity_s = arity s in
  let rec has_compat_rt t =
    (arity t = arity_s && types_compat t s)
    ||
    match t with
    | Fun (_, _, rt) -> has_compat_rt rt
    | _ -> false
  in
  let poly_set =
    VarSet.fold
      (fun x acc -> if has_compat_rt (VarMap.find x env) then VarSet.add x acc else acc)
      (try TypeMap.find polyentry ret_env with Not_found -> VarSet.empty)
      VarSet.empty
  in
  VarSet.union concrete_set poly_set
;;

(** Initial environment *)

let init_tri_env =
  List.fold_left
    (fun acc (var, t) -> add_var var t acc)
    (VarMap.empty, TypeMap.empty, TypeMap.empty)
    [ (* These follow the order and specification of the Pervasives module
         	  https://caml.inria.fr/pub/docs/manual-ocaml/libref/Pervasives.html *)
      (* Comparisons *)
      ( "(=)",
        let a = Typevar (newtypevar ()) in
        Fun (a, no_eff, Fun (a, (true, false), Bool)) );
      ( "(<>)",
        let a = Typevar (newtypevar ()) in
        Fun (a, no_eff, Fun (a, (true, false), Bool)) );
      ("(<)", Fun (Int, no_eff, Fun (Int, (true, false), Bool)));
      ("(>)", Fun (Int, no_eff, Fun (Int, (true, false), Bool)));
      (*
        ("(<=)", let a = Typevar (newtypevar()) in
        Fun (a, no_eff, Fun (a, (true,false), Bool)));
        ("(>=)",
        let a = Typevar (newtypevar()) in
        Fun (a, no_eff, Fun (a, (true,false), Bool)));
      *)
      ( "compare",
        let a = Typevar (newtypevar ()) in
        Fun (a, no_eff, Fun (a, (true, false), Int)) );
      (*
        ("min", let a = Typevar (newtypevar()) in
        Fun (a, no_eff, Fun (a, (true,false), a)));
        ("max",
          let a = Typevar (newtypevar()) in
          Fun (a, no_eff, Fun (a, (true,false), a)));
        ("(==)",
          let a = Typevar (newtypevar()) in
          Fun (a, no_eff, Fun (a, (true,false), Bool)));
        ("(!=)",
          let a = Typevar (newtypevar()) in
          Fun (a, no_eff, Fun (a, (true,false), Bool)));
      *)
      (* Boolean operations *)
      ("not", Fun (Bool, no_eff, Bool));
      ("(&&)", Fun (Bool, no_eff, Fun (Bool, no_eff, Bool)));
      ("(||)", Fun (Bool, no_eff, Fun (Bool, no_eff, Bool)));
      (* Integer arithmetic *)
      (*
        ("(~-)", Fun (Int, no_eff, Int));
        ("(~+)", Fun (Int, no_eff, Int));
      *)
      ("succ", Fun (Int, no_eff, Int));
      ("pred", Fun (Int, no_eff, Int));
      ("(+)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("(-)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("( * )", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("(/)", Fun (Int, no_eff, Fun (Int, (true, false), Int)));
      ("(mod)", Fun (Int, no_eff, Fun (Int, (true, false), Int)));
      ("abs", Fun (Int, no_eff, Int));
      (*
        ("max_int", Int);
        ("min_int",        Int);
      *)
      (* Bitwise operations *)
      ("(land)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("(lor)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("(lxor)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("lnot", Fun (Int, no_eff, Int));
      ("(lsl)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("(lsr)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("(asr)", Fun (Int, no_eff, Fun (Int, no_eff, Int)))
      (* Floating-point arithmetic *)
      (*
        ("(~-.)",          Fun (Float, no_eff, Float));
        ("(~+.)",          Fun (Float, no_eff, Float));
      *);
      ("(+.)", Fun (Float, no_eff, Fun (Float, no_eff, Float)));
      ("(-.)", Fun (Float, no_eff, Fun (Float, no_eff, Float)));
      ("( *. )", Fun (Float, no_eff, Fun (Float, no_eff, Float)));
      ("(/.)", Fun (Float, no_eff, Fun (Float, no_eff, Float)));
      ("( ** )", Fun (Float, no_eff, Fun (Float, no_eff, Float)));
      ("(sqrt)", Fun (Float, no_eff, Float));
      ("(exp)", Fun (Float, no_eff, Float));
      (* TODO: add other floating-point operations? *)
      (* String operations *)
      ("(^)", Fun (String, no_eff, Fun (String, no_eff, String)));
      (* Character operations *)
      (* Unit operations *)
      ( "ignore",
        let a = Typevar (newtypevar ()) in
        Fun (a, no_eff, Unit) );
      (* String conversion functions *)
      ("string_of_bool", Fun (Bool, no_eff, String));
      ("bool_of_string", Fun (String, (true, false), Bool));
      ("string_of_int", Fun (Int, no_eff, String));
      ("int_of_string", Fun (String, (true, false), Int));
      ("string_of_float", Fun (Float, no_eff, String));
      ("float_of_string", Fun (String, (true, false), Float));
      (* Pair operations *)
      (* List operations *)
      ( "(@)",
        let a = Typevar (newtypevar ()) in
        Fun (List a, no_eff, Fun (List a, no_eff, List a)) );
      (* Input/output *)
      (* Output functions on standard output *)
      ("print_string", Fun (String, (true, false), Unit));
      ("print_int", Fun (Int, (true, false), Unit));
      ("print_float", Fun (Float, (true, false), Unit));
      ("print_endline", Fun (String, (true, false), Unit));
      ("print_newline", Fun (Unit, (true, false), Unit));
      (* Output functions on standard error *)
      (*
        ("prerr_string",   Fun (String, (true,false), Unit));
        ("prerr_int",      Fun (Int, (true,false), Unit));
        ("prerr_endline",  Fun (String, (true,false), Unit));
        ("prerr_newline",  Fun (Unit, (true,false), Unit));
      *)
      (* Input functions on standard input *)
      (* General output functions *)
      (* General input functions *)
      (* Operations on large files *)
      (* References *)
      (* Result type *)
      (* Operations on format strings *)
      (* Program termination *)
      ( "exit",
        let a = Typevar (newtypevar ()) in
        Fun (Int, (true, false), a) );
      (*
        ("at_exit",        Fun (Fun (Unit, (true,false), Unit), (true,false), Unit));
      *)
      (* More list operations from List module *)
      ( "List.hd",
        let a = Typevar (newtypevar ()) in
        Fun (List a, (true, false), a) );
      ( "List.tl",
        let a = Typevar (newtypevar ()) in
        Fun (List a, (true, false), List a) )
      (*
        ("List.concat",    let a = Typevar (newtypevar()) in
        Fun (List (List a), no_eff, List a));
      *)
    ]
;;

(** Generators *)

(* Provides operations over a local cache that is used by a generator  *)
let new_cache () =
  let cache = ref [] in
  let to_cache fl = cache := fl :: !cache in
  let get_cache_lst () = !cache in
  let clear_cache () = cache := [] in
  (to_cache, get_cache_lst, clear_cache)
;;

module StaticGenerators = struct
  let alpha_gen =
    let a_code = int_of_char 'a' in
    let z_code = int_of_char 'z' in
    Gen.map char_of_int (Gen.int_range a_code z_code)
  ;;

  let var_gen = Gen.map (String.make 1) alpha_gen
  let string_gen = Gen.small_string ~gen:alpha_gen
  let str_to_str = Printf.sprintf "%S"
  let sqrt i = int_of_float (Pervasives.sqrt (float_of_int i))

  let int_gen =
    Gen.(
      frequency [ (10, small_int); (5, int); (1, oneofl [ min_int; -1; 0; 1; max_int ]) ])
  ;;

  let float_gen =
    Gen.frequency
      [ (5, Gen.float);
        ( 5,
          Gen.oneofl
            [ Float.nan;
              Float.neg_infinity;
              min_float;
              -1.;
              -0.;
              0.;
              Float.epsilon;
              1.;
              max_float;
              Float.infinity
            ] )
      ]
  ;;

  (* Generate a possibly repeated floating-point number *)
  let float_gen_with_rep_thunk () =
    let to_cache, get_cache_lst, _ = new_cache () in
    let from_cache_gen rs = (Gen.oneofl @@ get_cache_lst ()) rs in
    fun rs ->
      match get_cache_lst () with
      | [] ->
        Gen.map
          (fun fl ->
            to_cache fl;
            fl)
          float_gen
          rs
      | _xs ->
        Gen.map
          (fun fl ->
            if List.mem fl (get_cache_lst ())
            then fl
            else (
              to_cache fl;
              fl))
          (Gen.frequency [ (2, float_gen); (8, from_cache_gen) ])
          rs
  ;;

  let eff_gen = Gen.oneofl [ (false, false); (true, false) ]

  let type_gen =
    (* Generates ground types (sans type variables) *)
    Gen.fix (fun recgen n ->
        let base_types = [ Unit; Int; Float; Bool; String ] in
        if n = 0
        then Gen.oneofl base_types
        else
          Gen.frequency
            [ (* Generate no alphas *)
              (4, Gen.oneofl base_types);
              (1, Gen.map (fun t -> List t) (recgen (n / 2)));
              ( 1,
                Gen.map3
                  (fun t e t' -> Fun (t, e, t'))
                  (recgen (n / 2))
                  eff_gen
                  (recgen (n / 2)) )
            ])
  ;;
end

(** {!Context} is used to store the state of generator for the program that is being
  generated *)
module type Context = sig
  (** stateful float generator with value repetitions *)
  val float_gen_with_rep : float Gen.t
end

module FreshContext () : Context = struct
  let float_gen_with_rep = StaticGenerators.float_gen_with_rep_thunk ()
end

module GeneratorsWithContext (Ctx : Context) = struct
  open StaticGenerators

  (* Type-directed literal generator *)
  let rec literal_gen t eff size =
    match t with
    | Unit -> Gen.return LitUnit
    | Int -> Gen.map (fun i -> LitInt i) int_gen
    | Float -> Gen.map (fun f -> LitFloat f) float_gen
    | Bool -> Gen.map (fun b -> LitBool b) Gen.bool
    | String -> Gen.map (fun s -> LitStr s) string_gen
    | List (Typevar _) -> Gen.return (LitList [])
    | List t ->
      if size = 0
      then Gen.return (LitList [])
      else
        Gen.map
          (fun ls -> LitList ls)
          (Gen.list_size (Gen.int_bound (sqrt size)) (literal_gen t eff (sqrt size)))
    (*     (Gen.list_size (Gen.int_bound (size/2)) (literal_gen t eff (size/2))) *)
    (* FIXME: - one element should/can have effect, if 'eff' allows *)
    (*        - list items should be able to contain arbitrary effectful exps *)
    | Typevar _ -> failwith "literal_gen: typevar arg. should not happen"
    | Fun _ -> failwith "literal_gen: funtype arg. should not happen"
  ;;

  (* Sized generator of variables according to the LIT rule
   @param env  : surrounding environment
   @param s    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

   --------------------- (LIT)
       env |- l : s
*)
  let lit_rules _env s eff size =
    let rec list_of_fun = function
      | List s -> list_of_fun s
      | Fun _ -> true
      | _ -> false
    in
    match s with
    | List s when list_of_fun s -> []
    | Unit | Int | Float | Bool | String | List _ ->
      [ (6, Gen.map (fun l -> Some (Lit l)) (literal_gen s eff size)) ]
    | Fun _ | Typevar _ -> []
  ;;

  (* Sized generator of variables according to the VAR rule
   @param env  : surrounding environment
   @param s    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

      (t:s) \in env
   --------------------- (VAR)
       env |- t : s
*)
  let var_rules env s _eff _size =
    (* vars have no immediate effect, so 'eff' param is ignored *)
    let candvars = VarSet.elements (lookup_type (normalize_eff s) env) in
    let arity_s = arity s in
    let candvars' =
      List.filter
        (fun x ->
          match lookup_var x env with
          | Some t -> arity t = arity_s && types_compat t s
          | None ->
            failwith ("var_rules: found variable " ^ x ^ " without associated type"))
        candvars
    in
    List.map (fun var -> (1, Gen.return (Some (Variable (s, var))))) candvars'
  ;;

  (* Sized generator of lambda terms according to the LAM rule
   @param env  : surrounding environment
   @param u    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

               (x:s), env |- m : t
    -------------------------------------------- (LAM)
       env |- (fun (x:s) -> m) : s -> t
*)
  let rec lam_rules env u _eff size =
    (* lams have no immediate effect, so 'eff' param is ignored *)
    let gen s eff t =
      Gen.(
        var_gen >>= fun x ->
        list_permute_term_gen_outer (add_var x s env) t eff (size / 2) >>= function
        | None -> return None
        | Some m ->
          let myeff = imm_eff m in
          return (Some (Lambda (Fun (s, myeff, imm_type m), x, s, m))))
    in
    match u with
    | Unit | Int | Float | Bool | String | List _ | Typevar _ -> []
    | Fun (s, e, t) -> [ (8, gen s e t) ]

  (* Sized generator of applications (calls) according to the APP rule
   @param env  : surrounding environment
   @param t    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

       env |- f : s -> t     env |- x : s
    ---------------------------------------- (APP)
                 env |- f x : t
*)
  and app_rules env t eff size =
    let open Gen in
    let from_type funeff argeff s =
      list_permute_term_gen_outer env (Fun (s, eff, t)) funeff (size / 2) >>= function
      | None -> Gen.return None
      | Some f ->
        list_permute_term_gen_outer env s argeff (size / 2) >>= function
        | None -> Gen.return None
        | Some x ->
          (match imm_type f with
          | Fun (_, e, frange) ->
            let funeff = imm_eff f in
            let argeff = imm_eff x in
            let ef, ev = eff_join e (eff_join funeff argeff) in
            let eff' = (ef, ev || (fst funeff && fst argeff)) in
            if eff_leq eff' eff
            then Gen.return (Some (App (frange, f, imm_type x, x, eff')))
            else
              (*Gen.return None*)
              failwith "app_rules generated application with too big effect"
          | _ ->
            failwith
              ("app_rules generated application with non-function  "
              ^ " t is "
              ^ type_to_str ~effannot:true t
              ^ " f is "
              ^ term_to_ocaml ~typeannot:false f
              ^ " imm_type f is "
              ^ type_to_str ~effannot:true (imm_type f)))
    in
    (* May generate eff in either operator or operand *)
    [ (4, type_gen (size / 2) >>= from_type eff no_eff);
      (4, type_gen (size / 2) >>= from_type no_eff eff)
    ]

  (* Sized generator of multi-argument applications (calls) according to the INDIR rule
   @param env  : surrounding environment
   @param t    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

     (f : rho1 -> ... -> rhon -> t) in env     env |- m1 : rho1  ...  env |- mn : rhon
   ------------------------------------------------------------------------------------- (INDIR)
                                  env |- f m1 ... mn : t
*)
  and indir_rules env t eff size =
    let mgu s t =
      let rec loop = function
        | [] -> None
        | r :: rs ->
          (match unify r t with
          | Sol u -> Some u
          | No_sol -> loop rs)
      in
      loop (get_return_types s)
    in
    let rec get_arg_types s t =
      match s with
      | s when types_compat s t -> []
      | Fun (s', _, t') -> s' :: get_arg_types t' t
      | s ->
        failwith
          ("get_arg_types: should not happen  s is "
          ^ type_to_str ~effannot:true s
          ^ " t is "
          ^ type_to_str ~effannot:true t)
    in
    (* returns the index of the first effect - or else the number of arguments *)
    let rec first_eff = function
      | s when types_compat s t || types_compat t s -> 0
      | Fun (_, e, t) -> if e = no_eff then 1 + first_eff t else 1
      | s -> failwith ("first_eff: should not happen  " ^ type_to_str ~effannot:true s)
    in
    (* recursively build application term argument by argument *)
    let rec apply term r_type n effacc = function
      | [] -> Gen.return (Some term)
      | arg :: args ->
        (* arg 'n' may have effect 'eff' *)
        let myeff = if n = 0 then eff else no_eff in
        Gen.( >>= )
          (list_permute_term_gen_outer env arg myeff (size / 2))
          (function
            | None -> Gen.return None
            | Some a ->
              (match r_type with
              | Fun (_, funeff, new_rtype) ->
                let my_actual_eff = eff_join funeff (imm_eff a) in
                (* actual effect *)
                let effacc' = eff_join my_actual_eff effacc in
                if eff_leq effacc' eff
                then
                  apply
                    (App (new_rtype, term, imm_type a, a, effacc'))
                    new_rtype
                    (n - 1)
                    effacc'
                    args
                else
                  failwith
                    "apply: overly effectful program generated. This should not happen."
              | _ ->
                failwith
                  "apply: non-function type expecting argument. This should not happen")
            )
    in
    let application s f =
      (* s is the unnormalized, effect-full type *)
      let f_term = Variable (s, f) in
      match mgu s t with
      | None ->
        failwith
          ("indir_rules, application: the return types of chosen variable "
          ^ f
          ^ ":"
          ^ type_to_str ~effannot:true s
          ^ " do not match goal type "
          ^ type_to_str ~effannot:true t)
      | Some sub ->
        (* goal type and candidate unify with some subst *)
        let goal_type = subst sub s in
        (* goal type may have free variables, which we need to inst. *)
        let ftvs = ftv goal_type in
        let rec build_subst vs =
          match vs with
          | [] -> Gen.return []
          | v :: vs ->
            Gen.map2 (fun sub t -> (v, t) :: sub) (build_subst vs) (type_gen (sqrt size))
        in
        Gen.( >>= ) (build_subst ftvs) (fun sub' ->
            let goal_type = subst sub' goal_type in
            let arg_types =
              try get_arg_types goal_type (subst sub t)
              with Failure exc ->
                print_endline ("s is " ^ type_to_str ~effannot:true s);
                print_endline
                  ("sub is "
                  ^ Print.list
                      (Print.pair
                         (fun id -> "'a" ^ string_of_int id)
                         (type_to_str ~effannot:true))
                      sub);
                print_endline
                  ("(subst sub s) is " ^ type_to_str ~effannot:true (subst sub s));
                print_endline ("t is " ^ type_to_str ~effannot:true t);
                failwith exc
            in
            let first_eff_index = first_eff goal_type in
            Gen.(
              (if first_eff_index = 0 then return 0 else int_bound (first_eff_index - 1))
              >>= fun n -> apply f_term goal_type n no_eff arg_types))
    in
    let normalized_t = normalize_eff t in
    let suitable_vars = lookup_return normalized_t env in
    (* this returns a set of cand. sans effects *)
    let f_type_map =
      let rec acc_rt_and_effect eff ty =
        (* check that all effects are leq eff and that rt is compat *)
        (if types_compat (normalize_eff ty) normalized_t
            (* (sans effects) types agree here *)
        then types_compat ty t
        else true)
        &&
        match ty with
        | Fun (_, e, ty') -> eff_leq e eff && acc_rt_and_effect eff ty'
        | _ -> true
      in
      (* there may be several variables with the same type *)
      VarSet.fold
        (fun f acc ->
          match lookup_var f env with
          | Some ty ->
            (match mgu ty t with
            (* some rt of receiver (sans effects) matches here *)
            | None ->
              failwith "f_type_pairs: couldn't find a subst, which should not happen"
            | Some sub ->
              let ty' = subst sub ty in
              (* receiver may have poly type, which is too effectful when inst *)
              if acc_rt_and_effect eff ty' then add_multi_map ty f acc else acc)
          | None -> failwith "f_type_pairs: lookup_var failed, which should not happen")
        suitable_vars
        TypeMap.empty
    in
    TypeMap.fold
      (fun s fs acc ->
        (4, Gen.( >>= ) (Gen.oneofl (VarSet.elements fs)) (application s)) :: acc)
      f_type_map
      []

  (* Sized generator of let according to the LET rule
   @param env  : surrounding environment
   @param t    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

       env |- m : s     env, (x:s) |- n : t
    ------------------------------------------ (LET)
           env |- let x:s = m in n : t
*)
  and let_rules env t eff size =
    let open Gen in
    let from_type s =
      var_gen >>= fun x ->
      list_permute_term_gen_outer env s eff (size / 2) >>= function
      | None -> return None
      | Some m ->
        list_permute_term_gen_outer (add_var x s env) t eff (size / 2) >>= function
        | None -> return None
        | Some n ->
          let myeff = eff_join (imm_eff m) (imm_eff n) in
          return (Some (Let (x, s, m, n, imm_type n, myeff)))
    in
    [ (6, type_gen (size / 2) >>= from_type) ]

  and if_rules env t eff size =
    let open Gen in
    let gen =
      list_permute_term_gen_outer env Bool eff (size / 3) >>= function
      | None -> return None
      | Some b ->
        list_permute_term_gen_outer env t eff (size / 3) >>= function
        | None -> return None
        | Some m ->
          let then_type = imm_type m in
          (match unify then_type t with
          | No_sol ->
            failwith
              ("if_rules: generated type "
              ^ type_to_str ~effannot:true then_type
              ^ " in then branch does not unify with goal type "
              ^ type_to_str ~effannot:true t)
          | Sol sub ->
            let subst_t = subst sub t in
            list_permute_term_gen_outer env subst_t eff (size / 3) >>= function
            | None -> return None
            | Some n ->
              let else_type = imm_type n in
              (match unify else_type subst_t with
              | No_sol ->
                failwith
                  ("if_rules: generated else branch type "
                  ^ type_to_str ~effannot:true else_type
                  ^ " does not unify with subst goal type "
                  ^ type_to_str ~effannot:true subst_t)
              | Sol sub' ->
                let mytype = subst sub' subst_t in
                let myeff = eff_join (imm_eff b) (eff_join (imm_eff m) (imm_eff n)) in
                return (Some (If (mytype, b, m, n, myeff)))))
    in
    [ (3, gen) ]

  and list_permute_term_gen_inner env goal size rules =
    let rec remove_at n xs =
      match (n, xs) with
      | 0, _ :: xs -> xs
      | n, x :: xs -> x :: remove_at (n - 1) xs
      | _ -> failwith "index out of bounds"
    in
    let elts_weighted xs =
      let _, ig =
        List.fold_left
          (fun (i, acc) (w, g) -> (i + 1, (w, Gen.pair (Gen.return i) g) :: acc))
          (0, [])
          xs
      in
      Gen.frequency ig
    in
    let to_term i = function
      | Some term -> Gen.return (Some term)
      | None ->
        let remaining_rules = remove_at i rules in
        list_permute_term_gen_inner env goal size remaining_rules
    in
    if rules = []
    then Gen.return None
    else Gen.(elts_weighted rules >>= fun (i, t) -> to_term i t)

  and list_permute_term_gen_outer env goal eff size =
    if size = 0
    then (
      let rules =
        List.concat [ lit_rules env goal eff size; var_rules env goal eff size ]
      in
      list_permute_term_gen_inner env goal size rules)
    else (
      let rules =
        List.concat
          [ lit_rules env goal eff size;
            (*var_rules env goal eff size;*)
            (* var rule is covered by indir with no args *)
            app_rules env goal eff size;
            lam_rules env goal eff size;
            indir_rules env goal eff size;
            let_rules env goal eff size;
            if_rules env goal eff size
          ]
      in
      list_permute_term_gen_inner env goal size rules)
  ;;

  let list_permute_term_gen_rec_wrapper env goal eff =
    Gen.sized (list_permute_term_gen_outer env goal eff)
  ;;

  (* TODO: Include more base types - requires also changing `printer_by_etype` *)
  let basetype_gen = Gen.oneofl [ Int; Float; String ]
  let term_gen = list_permute_term_gen_rec_wrapper init_tri_env

  let dep_term_gen =
    Gen.(
      basetype_gen >>= fun typ ->
      term_gen typ (true, false) >>= fun trm_opt ->
      match trm_opt with
      | None -> return None
      | Some trm -> return (Some (typ, trm)))
  ;;
end

(** Shrinker and actual testing *)

module Shrinker = struct
  let create_lit t =
    let to_term s = Some (Lit s) in
    match t with
    | Unit -> to_term LitUnit
    | Int -> to_term (LitInt (Gen.generate1 small_int.gen))
    | Float -> to_term (LitFloat (Gen.generate1 float.gen))
    | Bool -> to_term (LitBool (Gen.generate1 bool.gen))
    | String -> to_term (LitStr (Gen.generate1 StaticGenerators.string_gen))
    | List _ | Fun _ | Typevar _ -> None
  ;;

  (* determines whether x occurs free (outside a binding) in the arg. exp *)
  let rec fv x = function
    | Lit _ -> false
    | Variable (_, y) -> x = y
    | Lambda (_, y, _, m) -> if x = y then false else fv x m
    | App (_, m, _, n, _) -> fv x m || fv x n
    | Let (y, _, m, n, _, _) -> fv x m || if x = y then false else fv x n
    | If (_, b, m, n, _) -> fv x b || fv x m || fv x n
  ;;

  (* renames free occurrences of 'x' into 'y' *)
  let rec alpharename m x y =
    match m with
    | Lit _ -> m
    | Variable (t, z) -> if x = z then Variable (t, y) else m
    | Lambda (t, z, t', m') -> if x = z then m else Lambda (t, z, t', alpharename m' x y)
    | App (rt, m, at, n, e) -> App (rt, alpharename m x y, at, alpharename n x y, e)
    | Let (z, t, m, n, t', e) ->
      let m' = alpharename m x y in
      if x = z then Let (z, t, m', n, t', e) else Let (z, t, m', alpharename n x y, t', e)
    | If (t, b, n, n', e) ->
      If (t, alpharename b x y, alpharename n x y, alpharename n' x y, e)
  ;;

  let shrink_lit = function
    | LitInt i -> Iter.map (fun i' -> Lit (LitInt i')) (Shrink.int i)
    (* TODO how to shrink floats? *)
    | LitStr s -> Iter.map (fun s' -> Lit (LitStr s')) (Shrink.string s)
    | LitList ls -> Iter.map (fun ls' -> Lit (LitList ls')) (Shrink.list ls)
    | _ -> Iter.empty
  ;;

  let ( <+> ) = Iter.( <+> )

  let rec term_shrinker term =
    match term with
    | Lit l -> shrink_lit l
    | Variable (t, _) ->
      (match create_lit t with
      | Some c -> Iter.return c
      | _ -> Iter.empty)
    | Lambda (t, x, s, m) -> Iter.map (fun m' -> Lambda (t, x, s, m')) (term_shrinker m)
    | App (rt, m, at, n, e) ->
      (match create_lit rt with
      | Some c -> Iter.return c
      | None -> Iter.empty)
      <+> (if types_compat at rt then Iter.return n else Iter.empty)
      <+> (match m with
          | App (_, _, at', n', _) when types_compat at' rt -> Iter.return n'
          | Lambda (_, x, s, m') ->
            if fv x m'
            then Iter.return (Let (x, s, n, m', rt, e))
            else Iter.of_list [ m'; Let (x, s, n, m', rt, e) ]
          | Let (x, t, m', n', _, _) ->
            if fv x n
            then (
              (* potential var capt.*)
              let x' = newvar () in
              Iter.return
                (Let (x', t, m', App (rt, alpharename n' x x', at, n, e), rt, e)))
            else Iter.return (Let (x, t, m', App (rt, n', at, n, e), rt, e))
          | _ -> Iter.empty)
      <+> Iter.map (fun m' -> App (rt, m', at, n, e)) (term_shrinker m)
      <+> Iter.map (fun n' -> App (rt, m, at, n', e)) (term_shrinker n)
    | Let (x, t, m, n, s, e) ->
      (match create_lit s with
      | Some c -> Iter.return c
      | _ -> Iter.empty)
      <+> (match (fv x n, m) with
          | false, Let (x', t', m', _, _, _) ->
            if fv x' n
            then (
              (* potential var capt.*)
              let y = newvar () in
              Iter.of_list [ n; Let (y, t', m', n, s, e) ])
            else Iter.of_list [ n; Let (x', t', m', n, s, e) ]
          | false, _ -> Iter.return n
          | true, _ -> Iter.empty)
      <+> Iter.map (fun m' -> Let (x, t, m', n, s, e)) (term_shrinker m)
      <+> Iter.map (fun n' -> Let (x, t, m, n', s, e)) (term_shrinker n)
    | If (t, b, m, n, e) ->
      (match create_lit t with
      | Some c -> Iter.return c
      | _ -> Iter.empty)
      <+> Iter.of_list [ n; m ]
      <+> (match b with
          | Lit _ -> Iter.empty
          | Variable (_, _) -> Iter.empty
          | _ ->
            let x = newvar () in
            Iter.return (Let (x, Bool, b, If (t, Variable (Bool, x), m, n, e), t, e)))
      <+> Iter.map (fun b' -> If (t, b', m, n, e)) (term_shrinker b)
      <+> Iter.map (fun m' -> If (t, b, m', n, e)) (term_shrinker m)
      <+> Iter.map (fun n' -> If (t, b, m, n', e)) (term_shrinker n)
  ;;

  let dep_term_shrinker (typ, term) = Iter.pair (Iter.return typ) (term_shrinker term)

  let wrapper shrinker op_term =
    match op_term with
    | None -> Iter.empty
    | Some term -> Iter.map (fun t -> Some t) (shrinker term)
  ;;

  let shrinker term = wrapper term_shrinker term
  let wrapped_dep_term_shrinker dep_term = wrapper dep_term_shrinker dep_term
end

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
let rec tcheck_lit l =
  match l with
  | LitUnit -> (Unit, no_eff)
  | LitInt _ -> (Int, no_eff)
  | LitFloat _ -> (Float, no_eff)
  | LitBool _ -> (Bool, no_eff)
  | LitStr _ -> (String, no_eff)
  | LitList l ->
    let etyp =
      List.fold_left
        (fun typacc elem ->
          let etyp, _ = tcheck_lit elem in
          if types_compat typacc etyp (* if typacc is a generalization of etyp *)
          then etyp
          else if types_compat etyp typacc (* if etyp is a generalization of typeacc *)
          then typacc
          else
            failwith
              ("tcheck_lit: elements in list literal disagree"
              ^ "  typacc is "
              ^ type_to_str ~effannot:true typacc
              ^ "  etyp is "
              ^ type_to_str ~effannot:true etyp))
        (Typevar (newtypevar ()))
        l
    in
    (List etyp, no_eff)
;;

let rec tcheck env term =
  match term with
  | Lit l -> tcheck_lit l
  | Variable (t, v) ->
    (try
       let et = VarMap.find v env in
       if types_compat et t (* annotation may be more concrete then inferred type *)
       then (et, no_eff)
       else failwith "tcheck: variable types disagree"
     with Not_found -> failwith "tcheck: unknown variable")
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
                  failwith
                    ("tcheck: effect annotation disagree in application"
                    ^ "  ceff is "
                    ^ eff_to_str ceff
                    ^ "  j_eff is "
                    ^ eff_to_str j_eff))
              else
                failwith
                  ("tcheck: argument types disagree in application"
                  ^ "  ntyp is "
                  ^ type_to_str ~effannot:true ntyp
                  ^ "  at is "
                  ^ type_to_str ~effannot:true at)
            | No_sol ->
              failwith
                ("tcheck: argument types do not unify in application"
                ^ "  ntyp is "
                ^ type_to_str ~effannot:true ntyp
                ^ "  at is "
                ^ type_to_str ~effannot:true at))
          else
            failwith
              ("tcheck: function types disagree in application"
              ^ ("  sub is "
                ^ Print.list
                    (Print.pair
                       (fun id -> "'a" ^ string_of_int id)
                       (type_to_str ~effannot:true))
                    sub)
              ^ "  mtyp is "
              ^ type_to_str ~effannot:true mtyp
              ^ "  (Fun (at,ceff,rt)) is "
              ^ type_to_str ~effannot:true (Fun (at, ceff, rt)))
        | No_sol ->
          failwith
            ("tcheck: function types do not unify in application"
            ^ "  mtyp is "
            ^ type_to_str ~effannot:true mtyp
            ^ "  (Fun (at,ceff,rt)) is "
            ^ type_to_str ~effannot:true (Fun (at, ceff, rt))))
      else failwith "tcheck: application has subexprs with eff"
    | _ -> failwith "tcheck: application of non-function type")
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
          failwith
            ("tcheck: let-effect disagrees with annotation"
            ^ "  leff is "
            ^ eff_to_str leff
            ^ "  j_eff is "
            ^ eff_to_str j_eff))
      else
        failwith
          ("tcheck: let-body's type disagrees with annotation: "
          ^ "ntyp is "
          ^ type_to_str ~effannot:true ntyp
          ^ "  ltyp is "
          ^ type_to_str ~effannot:true ltyp)
    else failwith "tcheck: let-bound type disagrees with annotation"
  | Lambda (t, x, s, m) ->
    let mtyp, meff = tcheck (VarMap.add x s env) m in
    let ftyp = Fun (s, meff, mtyp) in
    if types_compat ftyp t
    then (ftyp, no_eff)
    else
      failwith
        ("tcheck: Lambda's type disagrees with annotation: "
        ^ "ftyp is "
        ^ type_to_str ~effannot:true ftyp
        ^ "  t is "
        ^ type_to_str ~effannot:true t)
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
              else failwith "tcheck: If's branch effects disagree with annotation"
            else
              failwith
                ("tcheck: If's else branch type disagrees with annotation: "
                ^ "  term is "
                ^ term_to_ocaml ~typeannot:false term
                ^ "  ntyp is "
                ^ type_to_str ~effannot:true ntyp
                ^ "  (subst sub ntyp) is "
                ^ type_to_str ~effannot:true (subst sub ntyp)
                ^ "  t is "
                ^ type_to_str ~effannot:true t)
          else
            failwith
              ("tcheck: If's then branch type disagrees with annotation: "
              ^ "  term is "
              ^ term_to_ocaml ~typeannot:false term
              ^ "  mtyp is "
              ^ type_to_str ~effannot:true mtyp
              ^ "  (subst sub mtyp) is "
              ^ type_to_str ~effannot:true (subst sub mtyp)
              ^ "  t is "
              ^ type_to_str ~effannot:true t)
        | No_sol ->
          failwith
            ("tcheck: If's branch types do not unify:  "
            ^ "  term is "
            ^ term_to_ocaml ~typeannot:false term
            ^ "  mtyp is "
            ^ type_to_str ~effannot:true mtyp
            ^ "  ntyp is "
            ^ type_to_str ~effannot:true ntyp))
      else failwith "tcheck: If's condition effect disagrees with annotation"
    else failwith "tcheck: If with non-Boolean condition"
;;

let print_wrap t =
  Let
    ( "i",
      Int,
      t,
      App
        ( Unit,
          Variable (Fun (Int, (true, false), Unit), "print_int"),
          Int,
          Variable (Int, "i"),
          (true, false) ),
      Unit,
      (true, false) )
;;

let printer_by_etype typ =
  let fun_name, printer_typ_opt =
    match typ with
    | Int -> ("print_int", lookup_var "print_int" init_tri_env)
    | Float -> ("print_float", lookup_var "print_float" init_tri_env)
    | String -> ("print_string", lookup_var "print_string" init_tri_env)
    | Unit | Typevar _ | List _ | Fun _ | Bool ->
      failwith
        "printer_by_etype: such base type should not be generated (not implemented)"
  in
  match printer_typ_opt with
  | Some typ -> Variable (typ, fun_name)
  | None -> failwith "printer_by_etype: printer for this type is unavailable."
;;

let rand_print_wrap typ trm =
  Let
    ( "x",
      typ,
      trm,
      App (Unit, printer_by_etype typ, typ, Variable (typ, "x"), (true, false)),
      Unit,
      (true, false) )
;;

module Arbitrary = struct
  (* TODO: Is it correct to name a function using suffix `_gen`
          if it is of type `'a arbitrary`
  *)
  let term_gen_by_type typ =
    make
      ~print:(Print.option (term_to_ocaml ~typeannot:false))
      ~shrink:Shrinker.shrinker
      (fun rs ->
        let module Gener = GeneratorsWithContext (FreshContext ()) in
        Gener.term_gen typ (true, false) rs)
  ;;

  let int_term_gen = term_gen_by_type Int

  let typegen =
    make
      ~print:type_to_str
      Gen.(
        frequency
          [ (1, map (fun i -> Typevar i) (oneofl [ 1; 2; 3; 4; 5 ]));
            (6, sized StaticGenerators.type_gen)
          ])
  ;;

  (* Arbitrary type-dependent term generator - both the term and its type are generated by
  the same random seed *)
  let arb_dep_term_with_cache =
    make
      ~print:
        (let printer (_typ, trm) = term_to_ocaml ~typeannot:false trm in
         Print.option printer)
      ~shrink:Shrinker.wrapped_dep_term_shrinker
      (fun rs ->
        let module Gener = GeneratorsWithContext (FreshContext ()) in
        Gener.dep_term_gen rs)
  ;;
end

let unify_funtest =
  Test.make
    ~count:1000
    ~name:"unify functional"
    (pair Arbitrary.typegen Arbitrary.typegen)
    (fun (ty, ty') ->
      match unify ty ty' with
      | No_sol -> ty <> ty'
      | Sol t ->
        let sty = subst t ty in
        let sty' = subst t ty' in
        types_compat sty sty' || types_compat sty' sty)
;;

(* FIXME: update to arb_dep_term *)
let gen_classify =
  Test.make
    ~count:1000
    ~name:"classify gen"
    (make
       ~collect:(fun t -> if t = None then "None" else "Some")
       (gen Arbitrary.int_term_gen))
    (fun _ -> true)
;;

let can_compile_test =
  let counter = ref 1 in
  let file = "generated_tests/ocamltest.ml" in
  Test.make
    ~count:500
    ~long_factor:10
    ~name:"generated term passes OCaml's typecheck"
    Arbitrary.arb_dep_term_with_cache
    (fun t_opt ->
      t_opt
      <> None
      ==>
      match t_opt with
      | None -> false
      | Some (_typ, trm) ->
        (try
           let gened_src = term_to_ocaml trm in
           write_prog (Printf.sprintf "(* %i *) " !counter ^ gened_src) file;
           incr counter;
           0 = Sys.command ("ocamlc -w -5@20-26 " ^ file)
         with _ -> false))
;;

let type_check_test =
  Test.make
    ~count:500
    ~name:"generated term type checks"
    Arbitrary.arb_dep_term_with_cache
    (fun t_opt ->
      t_opt
      <> None
      ==>
      match t_opt with
      | None -> false
      | Some (typ, trm) ->
        let env, _, _ = init_tri_env in
        let typ', eff = tcheck env trm in
        types_compat typ typ' && eff_leq eff (true, false))
;;

let int_eq_test =
  Test.make
    ~count:500
    ~name:"bytecode/native backends agree - int_eq_test"
    Arbitrary.int_term_gen
    (fun topt ->
      topt
      <> None
      ==>
      match topt with
      | None -> false
      | Some t -> is_native_byte_equiv (term_to_ocaml (print_wrap t)))
;;

let rand_eq_test typ =
  Test.make
    ~count:500
    ~name:"bytecode/native backends agree - term gen by given type"
    (Arbitrary.term_gen_by_type typ)
    (fun topt ->
      topt
      <> None
      ==>
      match topt with
      | None -> false
      | Some t -> is_native_byte_equiv (term_to_ocaml (rand_print_wrap typ t)))
;;

let dep_eq_test =
  Test.make
    ~count:500
    ~long_factor:10
    ~name:"bytecode/native backends agree - type-dependent term generator"
    Arbitrary.arb_dep_term_with_cache
    (fun dep_t_opt ->
      dep_t_opt
      <> None
      ==>
      match dep_t_opt with
      | None -> false
      | Some (typ, trm) ->
        is_native_byte_equiv @@ term_to_ocaml @@ rand_print_wrap typ trm)
;;

(* The actual call to QCheck_runner.run_tests_main is located in effmain.ml *)
