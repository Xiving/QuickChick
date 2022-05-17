open Constrexpr
open Error

open GenericLib
open Pp

open Libnames (*I think this is where qualid is*)
open Names (*I think this is where Id.t is*)
open UnifyQC

(*
 make clean
 make install
 make -C ..

 emacs commands compile and recompile
*)


(*
data Term = Term Ctr [Term] | Hole String Hole deriving (Eq, Show)

data Constructor = Constructor String [(String, [Term])] [([Term], Term)] [Term] Term
--                              ^ other relations being called ^ recursive calls ^output As ^output T
data Relation = Relation String [Constructor] *)

(*
The plan is that I will use vars directly instead of holes.
genericLib already gives me vars where I need them, and they already have the exact behavior that I want.
*)

type ctr_data =
  (var * dep_type) list (*forall variables*)
  * dep_type list list (*recursive calls*)
  * (ty_ctr * dep_type list) list (*nonrecursive calls*)
  * dep_type list (*output parameters*)

let convertConstructor (me : ty_ctr) (ctr : dep_type) : ctr_data =
  let rec convertConstructorAux (ctr : dep_type) (me : ty_ctr) vs rs os : ctr_data =
    match ctr with
    | DProd  ((v, dt1), dt2) -> convertConstructorAux dt2 me ((v , dt1) :: vs) rs os
    | DTyCtr (tc, dts) -> (vs , rs , os , dts)
    | DArrow (DTyCtr (c , dts), dt2) -> if c == me then
      convertConstructorAux dt2 me vs (dts :: rs) os
      else
      convertConstructorAux dt2 me vs rs ((c , dts) :: os)
    | _ -> failwith ("convertConstructor: " ^ dep_type_to_string ctr)
    (* | DNot dt -> 
    | DTyParam tp -> 
    | DCtr (c, dts) ->
    | DTyVar v -> 
    | DApp (dt, dts) ->
    | DHole ->  *)
  in
  convertConstructorAux ctr me [] [] []

let convertBack (me : ty_ctr) ((vs , rs , os , outs) : ctr_data) : dep_type =
    let rec convertVars vs ty : dep_type =
      match vs with
      | [] -> ty
      | (v :: vs) -> convertVars vs (DProd (v , ty))
    in
    let rec convertRecCalls rs ty : dep_type =
      match rs with
      | [] -> ty
      | (r :: rs) -> convertRecCalls rs (DArrow ((DTyCtr (me , r)), ty))
    in
    let rec convertOtherCalls os ty : dep_type =
      match os with
      | [] -> ty
      | ((c, args) :: os) -> convertOtherCalls os (DArrow ((DTyCtr (c, args)), ty))
    in
    convertVars vs (convertRecCalls rs (convertOtherCalls os (DTyCtr (me, outs))))

(*Is this how you make a (Map var dep_type) in ocaml?*)
module IdMap = Map.Make(UnknownOrd)
type sub = dep_type IdMap.t

let rec sub_term (s : sub) (t : dep_type) : dep_type =
  match t with
  | DTyCtr (tc, dts) -> DTyCtr (tc, List.map (sub_term s) dts)
  | DArrow (dt1, dt2) -> DArrow (sub_term s dt1, sub_term s dt2)
  | DProd  ((v, dt1), dt2) -> DProd ((v , sub_term s dt1), sub_term s dt2)
  | DTyParam tp -> DTyParam tp
  | DCtr (c, dts) -> DCtr (c, List.map (sub_term s) dts)
  | DTyVar v -> IdMap.find v s
  | DApp (dt, dts) -> DApp (sub_term s dt, List.map (sub_term s) dts)
  | DNot dt -> DNot (sub_term s dt)
  | DHole -> DHole

let compose_sub  (sub1 : sub) (sub2 : sub) : sub =
    IdMap.union (fun _ _ _ -> failwith "shouldn't get here") (IdMap.map (sub_term sub1) sub2) sub1

let rec occurs (v : var) (t : dep_type) : bool =
  match t with
  | DTyCtr (tc, dts) -> List.exists (occurs v) dts
  | DArrow (dt1, dt2) -> occurs v dt1 || occurs v dt2
  | DProd  ((v, dt1), dt2) -> occurs v dt1 || occurs v dt2
  | DTyParam tp -> false
  | DCtr (c, dts) -> List.exists (occurs v) dts
  | DTyVar v' -> v == v'
  | DApp (dt, dts) -> occurs v dt || (List.exists (occurs v) dts)
  | DNot dt -> occurs v dt
  | DHole -> false

let rec unify (t1 : dep_type) (t2 : dep_type) : sub option =
  match t1, t2 with
  | DTyVar v, _ -> if occurs v t2 then None else Some (IdMap.singleton v t2)
  | DTyCtr (tc, dts), DTyCtr (tc', dts') -> unifys dts dts'
  | DArrow (dt1, dt2), DArrow (dt1', dt2') ->
      Option.bind (unify dt1 dt1') (fun sub1 ->
      Option.bind (unify (sub_term sub1 dt2) (sub_term sub1 dt2')) (fun sub2 ->
      Some (compose_sub sub1 sub2)))
  | DProd  ((v, dt1), dt2), DProd ((v', dt1'), dt2') ->
      Option.bind (unify dt1 dt1') (fun sub1 ->
      Option.bind (unify (sub_term sub1 dt2) (sub_term sub1 dt2')) (fun sub2 ->
      Some (compose_sub sub1 sub2)))
  | DTyParam tp, DTyParam tp' -> Some IdMap.empty
  | DCtr (c, dts), DCtr (c', dts') -> if not (c == c') then None
      else unifys dts dts'
  | DApp (dt, dts), DApp (dt', dts') -> 
      Option.bind (unify dt dt') (fun sub1 ->
      Option.bind (unifys (List.map (sub_term sub1) dts) (List.map (sub_term sub1) dts')) (fun sub2 ->
      Some (compose_sub sub1 sub2)))
  | DNot dt, DNot dt' -> unify dt dt'
  | DHole, DHole -> Some IdMap.empty
  | _, _ -> None

and unifys (t1s : dep_type list) (t2s : dep_type list) : sub option =
      match t1s, t2s with
      | [], [] -> Some IdMap.empty
      | (t1 :: t1s), (t2 :: t2s) -> 
        Option.bind (unify t1 t2) (fun s ->
          unifys (List.map (sub_term s) t1s) (List.map (sub_term s) t2s))
      | _, _ -> failwith "error, shouldn't get here!"
(*
TODO: I should double check that my implementation of unify is correct.
Shouldn't I apply the existing sub to terms before unifying?
   *)


(* P : c1 es | .... => P_ : c1_ es* .... *)
let renamer (ty_ctr, ty_params, ctrs, typ) : dep_dt =
  let ty_ctr' = gInjectTyCtr ((ty_ctr_to_string ty_ctr) ^ "_j") in
  let rec rename_dt = function
      | DTyCtr (tc, dts) ->
         if tc = ty_ctr then
           DTyCtr (ty_ctr', List.map rename_dt dts)
         else
           DTyCtr (tc, List.map rename_dt dts)
      | DArrow (dt1, dt2) ->
          DArrow (rename_dt dt1, rename_dt dt2)
      | DProd  ((v, dt1), dt2) ->
         DProd ((v, rename_dt dt1), rename_dt dt2)
      | DTyParam tp -> DTyParam tp
      | DCtr (c, dts) ->
         DCtr (c, List.map rename_dt dts)
      | DTyVar v -> DTyVar v
      | DApp (dt, dts) ->
         DApp (rename_dt dt, List.map rename_dt dts)
      | DNot dt -> DNot (rename_dt dt)
      | DHole -> DHole
  in
  let rename_dep_ctr (c, dt) : dep_ctr =
    let c' = injectCtr (constructor_to_string c ^ "_j") in
    (c', rename_dt dt)
  in
  (* let ctrs' = List.map rename_dep_ctr ctrs in *)
  let ctrs' = List.map (fun (c, dt) -> (injectCtr (constructor_to_string c ^ "_j")
    , convertBack ty_ctr' (convertConstructor ty_ctr dt))) ctrs in
  let typ' = rename_dt typ in
  (ty_ctr', ty_params, ctrs', typ')

let merge ind1 ind2 ind = 
(* (fun id => body) *)  
  match ind1 with 
  | { CAst.v = CLambdaN ([CLocalAssum ([{ CAst.v = Names.Name id1; CAst.loc = _loc2 }], _kind, _type)], body1); _ } ->
    (* Extract (x1,x2,...) if any, P and arguments *)
    let (p1, args1) =
      match body1 with 
      | { CAst.v = CApp (p, args); _ } -> (p, args)
      | _ -> qcfail "Merge/Not App"
    in     
    let dt1 : (ty_ctr * ty_param list * dep_ctr list * dep_type) = 
      match coerce_reference_to_dep_dt p1 with
      | Some dt -> msg_debug (str (dep_dt_to_string dt) ++ fnl()); dt 
      | None -> failwith "Not supported type"
    in
    msg_debug (str (dep_dt_to_string (renamer dt1)) ++ fnl ());
    define_new_inductive (renamer dt1)
  | _ -> qcfail "Merge/NotLam"
