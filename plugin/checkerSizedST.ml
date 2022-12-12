open Pp
open Util
open GenericLib
open CoqLib
open GenLib
open Error
open UnifyQC
open Names
open Constrexpr

(* arguments to handle_branch *)
let fail_exp (dt : coq_expr) : coq_expr = gSome dt g_false
let not_enough_fuel_exp (dt : coq_expr) : coq_expr = gNone dt                             

let ret_exp (dt : coq_expr) (c : coq_expr) = gSome dt c 

let ret_type (s : var) f = hole

let instantiate_existential_method = (gInject "enum")

let instantiate_existential_methodST (n : int) (pred : coq_expr) =
  gApp ~explicit:true (gInject "enumSuchThat")
    [ hole (* Implicit argument - type A *)
    ; pred
    ; hole (* Implicit instance *)]

let rec_method (rec_name : coq_expr) (init_size : coq_expr) (size : coq_expr) (n : int) (letbinds : unknown list option) (l : coq_expr list) =
  gApp rec_name (init_size :: size :: l)

(* For checkers, ignore the opt argument *)
let rec_bind (opt : bool) (m : coq_expr) (x : string) (f : var -> coq_expr) : coq_expr =
  gMatch m
    [ (injectCtr "Some", ["res_b" ] , fun [b] ->
      (* Why as clauses/returns? *)       
      gMatch (gVar b) 
        [ (injectCtr "true", [], fun _ -> f b)
        ; (injectCtr "false", [], fun _ -> fail_exp hole)
        ])
    ; (injectCtr "None", [], fun _ -> gNone hole ) 
    ]
  
let exist_bind (init_size : coq_expr) (opt : bool) (m : coq_expr) (x : string) (f : var -> coq_expr) : coq_expr =
  enumCheckerOpt m x f init_size
(*  (if opt then enumCheckerOpt else enumChecker) m x f init_size *)

let stMaybe (opt : bool) (g : coq_expr) (x : string) (checks : ((coq_expr -> coq_expr) * int) list) =
  let rec sumbools_to_bool x lst =
    match lst with
    | [] -> gTrueb
    | (chk, _) :: lst' ->
      matchDec (chk (gVar x)) (fun heq -> gFalseb) (fun hneq -> sumbools_to_bool x lst')
  in
  let bool_pred =
    gFun [x]
      (fun [x] -> sumbools_to_bool x checks)
  in
  (gApp (gInject (if opt then "suchThatMaybeOpt" else "suchThatMaybe"))
     [ g (* Use the generator provided for base generator *)
     ; bool_pred
  ])

let ret_type_dec (s : var) (left : coq_expr) (right : coq_expr) =
      gMatch (gVar s)
      [ (injectCtr "left", ["eq"], fun _ -> left)
      ; (injectCtr "right", ["neq"], fun _ -> right) ]

let check_expr (n : int) (scrut : coq_expr) (left : coq_expr) (right : coq_expr) (out_of_fuel : coq_expr) =
  gMatchReturn scrut
    "s" (* as clause *)
    (fun v -> ret_type v ret_type_dec)
    [ (injectCtr "Some", ["res_b" ] , fun [b] ->
      (* Why as clauses/returns? *)       
      gMatch (gVar b) 
        [ (injectCtr "true", [], fun _ -> left)
        ; (injectCtr "false", [], fun _ -> right)
        ])
    ; (injectCtr "None", [], fun _ -> out_of_fuel) 
    ]

let match_inp (inp : var) (pat : matcher_pat) (left : coq_expr) (right  : coq_expr) =
  msg_debug (str ("Match on input: ") ++ str (var_to_string inp) ++ fnl ());
  let ret v left right =
    construct_match (gVar v) ~catch_all:(Some right) [(pat, left)]
  in
  let rec uni_constr pat c ls =
    let uni_constr_mapper x = 
      match x with 
      | MatchU _ -> true 
      | MatchCtr (c', ls') -> uni_constr x c' ls'
      | MatchParameter _ -> true
    in
    msg_debug (str (Printf.sprintf "Number of constructors is %d for first relation used in: %s" (num_of_ctrs c) (matcher_pat_to_string pat)) ++ fnl());
    num_of_ctrs c = 1 && List.for_all uni_constr_mapper ls
  in
  let catch_case = 
    match pat with 
    | MatchCtr (c, ls) -> 
       (* Leo: This is a hack totality check for unary matches *)
       if uni_constr pat c ls
       then (msg_debug (str "Goal matches single case, no pokematch needed" ++ fnl()); None)
       else (msg_debug (str "Goal matches multiple cases" ++ fnl()); Some right)
    | _ -> failwith "Toplevel match not a constructor?"
  in 
  construct_match_with_return
    (gVar inp) ~catch_all:(catch_case) "s" (fun v -> ret_type v ret)
    [(pat,left)]

type generator_kind = Base_gen | Ind_gen 
  
(* hoisting out base and ind gen to be able to call them from proof generation *)
let construct_generators
      (kind : generator_kind)
      (init_size : coq_expr)
      (size : coq_expr)
      (full_gtyp : coq_expr)
      (gen_ctr : ty_ctr)
      (* FIXME: includes the wrong type when deriving checker over relaition over an mutually recursive type *)
      (dep_type : dep_type)
      (ctrs : dep_ctr list)
      (rec_name : coq_expr)
      (input_ranges : range list)
      (init_umap : range UM.t)
      (init_tmap : dep_type UM.t)
      (result : Unknown.t)
  =
  msg_debug (str "Beginning checker construction" ++ fnl());
  (* partially applied handle_branch *)
  let handle_branch' : dep_ctr -> coq_expr * bool =
    handle_branch ["EnumSizedSuchThat"; "EnumSuchThat"] dep_type init_size
      (fail_exp full_gtyp) (not_enough_fuel_exp full_gtyp) (ret_exp full_gtyp)
      instantiate_existential_method instantiate_existential_methodST (exist_bind init_size)
      (rec_method rec_name init_size size) rec_bind
      stMaybe check_expr match_inp gLetIn gLetTupleIn
      gen_ctr init_umap init_tmap input_ranges result
  in
  let all_gens = List.map handle_branch' ctrs in
  let padNone =
    if List.exists (fun gb -> not (snd gb)) all_gens
    then [gNone gBool] else [] in
  match kind with
  | Base_gen ->
     List.map fst (List.filter snd all_gens) @ padNone
  | Ind_gen  ->
     List.map fst ((List.filter snd all_gens) @ (List.filter (fun x -> not (snd x)) all_gens))

let base_gens = construct_generators Base_gen
let ind_gens  = construct_generators Ind_gen              
              
(* Advanced Generators *)
let checkerSizedST
      (gen_ctr : ty_ctr)
      (ty_params : ty_param list)
      (ctrs : dep_ctr list)
      (dep_type : dep_type)
      (input_names : var list)
      (input_ranges : range list)
      (init_umap : range UM.t)
      (init_tmap : dep_type UM.t)
      (inputs : arg list)
      (result : Unknown.t)
      (rec_name : coq_expr) =
  msg_debug (str ("checkerSizedST (checkerSizedST.ml): ") ++ str (UM.fold (fun _ dt s -> String.concat ", " [s; (dep_type_to_string dt)]) init_tmap "") ++ fnl ());
  (* type constructor *)
  let coqTyCtr = gTyCtr gen_ctr in

  (* parameters of the type constructor *)
  let coqTyParams = List.map gTyParam ty_params in

  (* Unused, not exported... *)
  (* Fully applied type constructor *)
  let _full_dt = gApp ~explicit:true coqTyCtr coqTyParams in

  (* The type we are generating for -- not the predicate! *)
  let full_gtyp = (gType ty_params (UM.find result init_tmap)) in


  (* The type of the derived checker *)
  let gen_type = (gOption full_gtyp) in

  let aux_arb rec_name init_size size vars =
    gMatch (gVar size)
      [ (injectCtr "O", [],
         fun _ ->
           checker_backtracking
             (base_gens init_size (gVar size) full_gtyp gen_ctr dep_type ctrs rec_name
                input_ranges init_umap init_tmap result))
      ; (injectCtr "S", ["size'"],
         fun [size'] ->
         checker_backtracking 
           (ind_gens init_size (gVar size') full_gtyp gen_ctr dep_type ctrs rec_name
              input_ranges init_umap init_tmap result))
      ]
  in
  let lname_to_string (ln : lname) = match ln with
    {CAst.v = id; _} -> match id with
    | Name id' -> Id.to_string id'
    | Anonymous -> "Anonymous"
  in
  let binder_kind_to_string bkind =
    "bind_kind" 
  in
  let rec constr_expr_to_string cexpr = match cexpr with 
    | { CAst.v = expr } -> match expr with
      | CRef _ -> "CRef"
      | CFix _ -> "CFix"
      | CCoFix _ -> "CCoFix"
      | CProdN _ -> "CProdN"
      | CLambdaN _ -> "CLambdaN"
      | CLetIn _ -> "CLetIn"
      | CAppExpl _ -> "CAppExpl"
      | CApp ((_, cexpr1), _) -> constr_expr_to_string cexpr1
      | _ -> "otherwise"
  in
  let input_to_string (input : arg) : string =
    match (unwrap_arg input) with
    | CLocalAssum (lns, bkind, cexpr) ->
        Printf.sprintf "CLocalAssum(%s, %s, %s)" 
          (String.concat ", " (List.map lname_to_string lns))
          (binder_kind_to_string bkind) 
          (constr_expr_to_string cexpr)
    | _ -> "UNKNOWN INPUT TYPE"
  in

  let inputs_to_string (inputs : arg list) : string =
    String.concat ", " (List.map input_to_string inputs)
  in

  let generator_body : coq_expr =
    (* This might cause things to break *)
    let sizeVar = fresh_name "size" in
    gRecFunInWithArgs
      ~structRec:(Some sizeVar)
      ~assumType:(gen_type)
      "aux_arb"
      (gArg ~assumName:(gVar (fresh_name "init_size")) ()
       :: gArg ~assumName:(gVar sizeVar) () :: inputs) 
      (fun (rec_name, init_size::size::vars) -> aux_arb (gVar rec_name) (gVar init_size) size vars)
      (fun rec_name -> gFun ["size"] 
          (fun [size] -> gApp (gVar rec_name) 
              (gVar size :: gVar size :: List.map (fun i -> gVar (arg_to_var i)) inputs)
          ))
  in

  msg_debug (str ("Inputs: ") ++ str (inputs_to_string inputs) ++ fnl ());
  msg_debug (fnl () ++ fnl () ++ str "`Final body produced:" ++ fnl ());
  debug_coq_expr generator_body;
  msg_debug (fnl ());
  gRecord [("decOpt", generator_body)]
