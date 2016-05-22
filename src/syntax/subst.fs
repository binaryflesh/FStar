(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
// (c) Microsoft Corporation. All rights reserved
module FStar.Syntax.Subst

open FStar
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Util
open FStar.Ident

// VALS_HACK_HERE

(*
    force_uvar (t:term) 
        replaces any unification variable at the head of t
        with the term that it has been fixed to, if any.
*)
let rec force_uvar t = match t.n with
  | Tm_uvar (uv,_) ->
      begin
        match Unionfind.find uv with
          | Fixed t' -> force_uvar t'
          | _ -> t
      end
  | _ -> t

let rec force_delayed_thunk t = match t.n with
  | Tm_delayed(f, m) ->
    (match !m with
      | None -> 
        begin match f with 
            | Inr c -> let t' = force_delayed_thunk (c()) in m := Some t'; t'
            | _ -> t
        end
      | Some t' -> let t' = force_delayed_thunk t' in m := Some t'; t')
  | _ -> t

let rec compress_univ u = match u with 
    | U_unif u' -> 
      begin match Unionfind.find u' with 
        | Some u -> compress_univ u
        | _ -> u
      end
    | _ -> u
    
(********************************************************************************)
(*************************** Delayed substitutions ******************************)
(********************************************************************************)
(* A subst_t is a composition of parallel substitutions, expressed as a list of lists *)
let bv_to_string' = ref (fun (x:bv) -> failwith "Not initialized!")
let print_term'   = ref (fun (t:term) -> failwith "Not initialized!")
let print_univ'   = ref (fun (u:universe) -> failwith "Not initialized!")
let bv_to_string x = !bv_to_string' x
let print_term t = !print_term' t
let print_univ u = !print_univ' u

let renaming_elt_to_string = function
   | Index2Name(i, x) -> Util.format2 "Index2Name (%s, %s)" (string_of_int i) (bv_to_string x)
   | Name2Index(x, i) -> Util.format2 "Name2Index (%s, %s)" (bv_to_string x) (string_of_int i)
   | Name2Name(x, y)  -> Util.format2 "Name2Name(%s, %s)" (bv_to_string x) (bv_to_string y)
   | Index2Index(i, j) -> Util.format2 "Index2Index (%d, %d)" (string_of_int i) (string_of_int j)
   | UIndex2UName(i, u) -> Util.format2 "UIndex2Uname(%d, %s)" (string_of_int i) u.idText
   | UName2UIndex(u, i) -> Util.format2 "UName2UIndex (%s, %s)" u.idText (string_of_int i) 
   | UIndex2UIndex(i, j) -> Util.format2 "UIndex2UIndex (%d, %d)" (string_of_int i) (string_of_int j)
   | UName2UName(u, v) -> Util.format2 "UName2UName(%s, %s)" u.idText v.idText
let renaming_to_string r = 
    Util.format1 "Renaming[%s]" (r |> List.map renaming_elt_to_string |> String.concat "; ")

let instantiation_elt_to_string = function
   | Name2Term(x, t) -> Util.format2 "Name2Term(%s, %s)" (bv_to_string x) (print_term t)
   | UName2Univ(un, u) -> Util.format2 "UName2Univ(%s, %s)" un.idText (print_univ u)

let instantiation_to_string i = 
    Util.format1 "Instantiation[%s]" (i |> List.map instantiation_elt_to_string |> String.concat "; ")

 let subst_to_string s = 
    s |> List.map (function 
                   | Renaming r -> renaming_to_string r
                   | Instantiation i -> instantiation_to_string i) 
      |> String.concat "; " 

//Lookup a bound var in a parallel substitution
type renaming = list<renaming_subst>
type inst     = list<inst_subst>

let subst_index i s = 
    let rename_index a renaming = Util.find_map renaming (function 
        | Index2Name(i, x) when (i=a.index) -> 
          Some (bv_to_name (Syntax.set_range_of_bv x (Syntax.range_of_bv a)))
        | Index2Index(i, j) when (i=a.index) -> 
          Some (bv_to_tm ({a with index=j}))
        | _ -> None) 
    in
    match s with 
    | Renaming renaming -> rename_index i renaming
    | _ -> None

let subst_name x s = 
    let rename_name a renaming = Util.find_map renaming (function  
        | Name2Index (x, i) when bv_eq a x -> Some (bv_to_tm ({a with index=i})) 
        | Name2Name (x, y) when bv_eq a x -> Some (bv_to_name y)
        | _ -> None)
    in
    let instantiate x inst = Util.find_map inst (function
        | Name2Term(y, t) when bv_eq x y -> Some t
        | _ -> None)
    in
    match s with 
    | Renaming renaming  -> rename_name x renaming
    | Instantiation inst -> instantiate x inst


let subst_uindex i s = 
    let rename_uindex i renaming = Util.find_map renaming (function 
        | UIndex2UName (j, t) when (i=j) -> Some (U_name t)
        | UIndex2UIndex(j, k) when (i=j) -> Some (U_bvar k)
        | _ -> None)
    in
    match s with 
    | Renaming renaming -> rename_uindex i renaming
    | _ -> None

let subst_uname x s = 
    let rename_uname (x:univ_name) renaming = Util.find_map renaming (function 
        | UName2UIndex(y, i) when (x.idText=y.idText) -> Some (U_bvar i)
        | UName2UName (y, z) when (x.idText=y.idText) -> Some (U_name z)
        | _ -> None)
    in
    let instantiate_uname x inst = Util.find_map inst (function
        | UName2Univ(y, t) when (x.idText=y.idText) -> Some t
        | _ -> None)
    in
    match s with 
    | Renaming renaming  -> rename_uname x renaming
    | Instantiation inst -> instantiate_uname x inst


(* apply_until_some f s 
      applies f to each element of s until it returns (Some t)
*)
let rec apply_until_some f s = match s with
    | [] -> None
    | s0::rest ->
        match f s0 with
            | None -> apply_until_some f rest
            | Some st -> Some (rest, st)

let map_some_curry f x = function
    | None -> x
    | Some (a, b) -> f a b

let apply_until_some_then_map f s g t = 
    apply_until_some f s 
    |> map_some_curry g t

let rec subst_univ (s:subst_ts) u =
    let u = compress_univ u in
    match u with 
    | U_bvar x -> 
      apply_until_some_then_map (subst_uindex x) s subst_univ u
    | U_name x ->
      apply_until_some_then_map (subst_uname x) s subst_univ u
    | U_zero
    | U_unknown 
    | U_unif _ -> u
    | U_succ u -> U_succ (subst_univ s u)
    | U_max us -> U_max (List.map (subst_univ s) us)

(* s1 and s2 are each parallel substitutions
    e.g., s1 = [Name2Index(x, 0); Name2Index(y, 1)]
          s2 = [Index2Name(0, x'); Index2Name(1, y')]
    compose them to 
          s  = [Name2Name(x, x'); Name2Name(y, y')]
*)
let compose_renamings (s1:renaming) (s2:renaming) : renaming = 
   let find_and_remove f s = 
        let rec aux out s = match s with 
            | [] -> None, out
            | hd::tl -> if f hd then Some hd, out@tl
                        else aux (hd::out) tl in
        aux [] s in
 
   let find_name s x = 
     s |> find_and_remove (function
        | Name2Index(y, _)
        | Name2Name(y, _) -> bv_eq x y
        | _ -> false) in
 
   let find_index s i = 
     s |> find_and_remove (function
        | Index2Name(j, _) 
        | Index2Index(j, _) -> i=j
        | _ -> false) in

   let find_uindex s2 i = s2 |> find_and_remove (function
        | UIndex2UName (j, _)
        | UIndex2UIndex(j, _) -> i=j
        | _ -> false) in

   let find_uname s2 n = s2 |> find_and_remove (function
        | UName2UIndex(m, _) 
        | UName2UName (m, _) -> n.idText=m.idText 
        | _ -> false) in
             
   //consider applying (s1 . s2) to a term T
   //In general, given a substition as a list (var * term), 
   //the composition s1 . s2 is  
   //    s2 |> filter (fun (x, _) -> x not in dom s1)  
   //    @ map (fun (x, t) -> (x, s2 t) s1
   //However, our substitutions have more structure and we can optimize a bit further
   //First, we assume that s1 and s2 have non-overlapping domains
   let s2_orig = s2 in
   let comp = s1 |> List.fold_left (fun s2 s1_elt -> 
           match s1_elt with 
           | Index2Name(i, x) -> //opening i to x
                //assert (Index2*(i, _)) not in s2 (disjoint domains)
                //assert x is fresh identifer not occuring im T
                let s2_x, s2_remainder = find_name s2 x in
                begin match s2_x with 
                    | Some (Name2Index(_, j)) -> //closing x to j
                        if i=j 
                        then s2_remainder //they cancel
                        else Index2Index(i,j)::s2_remainder

                    | Some (Name2Name(_, y)) -> //renaming x to y
                        Index2Name(i, y)               //open i to y directly
                        ::s2_remainder                 //x does not occur in T, so no need to keep s2_x

                    | _ -> //must be None; nothing to compose with 
                        s1_elt
                        ::s2_remainder                 //s2_remainder == s2, up to reordering
                end

           | Name2Index(x, i) -> //closing x to i
                 //assert {NM(x, _), NT(x, _)} not in s2 (disjoint domains)
                 //de Bruijn index i does not appear in T
                 let s2_i, s2_remainder = find_index s2 i in

                 begin match s2_i with 
                    | Some (Index2Name(_, y)) ->  //open i to y; y is fresh
                      Name2Name(x, y)     //rename x to y in one step
                      ::s2_remainder      //i does not appear in T, so no need to keep s2_i
                    
                    | Some (Index2Index(_, j)) ->  //replace i to j
                      Name2Index(x, j)             //rename x to j in one step
                      ::s2_remainder
                      
                    | _ ->                //s2_i=None
                      s1_elt              //nothing to compose with
                      ::s2_remainder      //s2_remainder == s2, up to reordering
                 end

           | Index2Index(i, j) -> 
                 let s2_i, s2_remainder = find_index s2 i in
                 begin match s2_i with 
                    | Some (Index2Name(_, y)) ->  //open j to y; y is fresh
                      Index2Name(i, y)            //open i to y
                      ::s2_remainder              //j does not appear in T, so no need to keep s2_i

                    | Some (Index2Index(_, k)) ->  //replace j to k
                      Index2Index(i, k)            //rename i to k in one step
                      ::s2_remainder
                      
                    | _ ->                //s2_i=None
                      s1_elt              //nothing to compose with
                      ::s2_remainder      //s2_remainder == s2, up to reordering
                 end


           | Name2Name(x, y) -> //renaming x to y
                //assert {NM(x, _), NT(x, _)} not in s2 (disjoint domains)
                let s2_y, _ = find_name s2 y in
                begin match s2_y with
                    | Some (Name2Index(_, j)) -> //closing y to j
                      Name2Index(x, j)           //close x to j in 1 step
                      ::s2               //y may occur free in T; so keep it in s2

                    | _ ->                //s2_y=None
                      s1_elt              //nothing to compose with
                      ::s2
                end

           | UIndex2UName(i, n) ->             //i is opened to n; just like the DB(i, x) case
             let u_n, s2_remainder = find_uname s2 n in

             //n is fresh, i.e., n not in FV T
             //i not in dom s2
             begin match u_n with 
                | Some(UName2UIndex(_, j)) ->  //n is closed to j
                  if i=j
                  then s2_remainder
                  else UIndex2UIndex(i,j)
                       ::s2_remainder

                | Some(UName2UName (_, u)) ->   //subst n to u
                  UIndex2UName(i, u)            //open and subst i to u directly
                  ::s2_remainder                //n is fresh, so no need to keep u_n

                | _ ->                //u_n is None
                  s1_elt              //nothing to compose with  
                  ::s2_remainder      //s2_remainder == s2, up to reordering
              end
          
           | UName2UIndex(u, i) ->            //close universe name un with index i; just like the NM case
             let u_i, s2_remainder = find_uindex s2 i in
             begin match u_i with 
                | Some(UIndex2UName(_, v)) ->   //i is mapped to v
                  UName2UName(u, v)             //rename u to v in 1 step
                  ::s2_remainder      //i does not appear in T, so no need to keep u_i
 
                | Some(UIndex2UIndex(_, k)) ->   //i is mapped to k
                  UName2UIndex(u, k)
                  ::s2_remainder
                
                | _ ->                //u_i=None
                  s1_elt              //nothing to compose with
                  ::s2_remainder      //s2_remainder == s2, up to reordering
             end

          | UName2UName(u, v) ->              //like the NT case
            let u_i, s2_remainder = find_uname s2 v in
            begin match u_i with 
                | Some(UName2UIndex (_, i)) ->
                  UName2UIndex(u, i)
                  ::s2 //v may still be free in T

                | Some (UName2UName (_, w)) ->
                  UName2UName(u, w)
                  ::s2

                | _ -> 
                   s1_elt
                   ::s2_remainder
            end
         
           | UIndex2UIndex(i, j) -> 
                 let s2_i, s2_remainder = find_uindex s2 i in
                 begin match s2_i with 
                    | Some (UIndex2UName(_, y)) ->  //open j to y; y is fresh
                      UIndex2UName(i, y)            //open i to y
                      ::s2_remainder              //j does not appear in T, so no need to keep s2_i

                    | Some (UIndex2UIndex(_, k)) ->  //replace j to k
                      UIndex2UIndex(i, k)            //rename i to k in one step
                      ::s2_remainder
                      
                    | _ ->                //s2_i=None
                      s1_elt              //nothing to compose with
                      ::s2_remainder      //s2_remainder == s2, up to reordering
                 end)
    s2 in
//  let comp = comp |> remove_dups (fun a b -> 
//        match a, b with
//        | Name2Term(x, _), Name2Term(y, _) 
//        | Name2Name(x, _), Name2Name(y, _) 
//        | Name2Index(x, _), Name2Index(y, _) -> bv_eq x y 
//        | Index2Name(i, _), Index2Name(j, _)
//        | UIndex2Univ(i, _), UIndex2Univ(j, _) -> i=j
//        | UName2UIndex(x, _), UName2UIndex(y, _) 
//        | UName2Univ(x, _), UName2Univ(y, _) -> x.idText = y.idText
//        | _ -> false) in
//  printfn "Composing %s;\tand %s;\tto %s" (subst_to_string s1) (subst_to_string s2) (subst_to_string comp);
  comp


let compose_subst (s1:subst_ts) (s2:subst_ts) : subst_ts = 
    let composed = s1@s2 in
    List.fold_right (fun ri out -> match ri, out with 
        | Renaming re1, Renaming re2::tl -> Renaming (compose_renamings re1 re2)::tl
        | _ -> ri::out) [] composed

let shift n s = match s with 
    | Index2Name   (i, t) -> Index2Name   (i+n, t)
    | Index2Index  (i, j) -> Index2Index  (i+n, j+n)
    | Name2Index   (x, i) -> Name2Index   (x,   i+n)
    | UName2UIndex (x, i) -> UName2UIndex (x,   i+n)
    | UIndex2UName (i, x) -> UIndex2UName (i+n, x)
    | UIndex2UIndex(i, j) -> UIndex2UIndex(i+n, j+n)
    | UName2UName _
    | Name2Name _        -> s

let shift_renaming n s = List.map (shift n) s

let shift_subst n (s:subst_ts) = List.map (function 
    | Renaming s -> Renaming (shift_renaming n s)
    | x -> x) s
    
let rec subst' (s:subst_ts) t = 
  match s with
  | [] -> t 
  | _ ->
    let t0 = force_delayed_thunk t in 
    match t0.n with
        | Tm_constant _      //a constant cannot be substituted
        | Tm_fvar _          //fvars are never subject to substitution
        | Tm_uvar _ -> t0    //uvars are always resolved to closed terms

        | Tm_delayed(Inl(t', s'), m) ->
            //s' is the subsitution already associated with this node;
            //s is the new subsitution to add to it
            //compose substitutions by concatenating them
            //the order of concatenation is important!
          mk_Tm_delayed (Inl (t', compose_subst s' s)) t.pos

        | Tm_delayed(Inr _, _) -> 
          failwith "Impossible: force_delayed_thunk removes lazy delayed nodes"

        | Tm_bvar a ->
          apply_until_some_then_map (subst_index a) s subst' t0

        | Tm_name a -> 
          apply_until_some_then_map (subst_name a) s subst' t0

        | Tm_type u -> 
          mk (Tm_type (subst_univ s u)) None t0.pos 
          
        | _ -> mk_Tm_delayed (Inl(t0, s))  t.pos

and subst_flags' s flags =
    flags |> List.map (function
        | DECREASES a -> DECREASES (subst' s a)
        | f -> f)

and subst_comp_typ' s t = 
match s with
  | [] -> t
  | _ ->
    {t with result_typ=subst' s t.result_typ;
            flags=subst_flags' s t.flags;
            effect_args=List.map (fun (t, imp) -> subst' s t, imp) t.effect_args}

and subst_comp' s t =
 match s with
  | [] -> t
  | _ ->
    match t.n with
      | Total t -> mk_Total (subst' s t)
      | GTotal t -> mk_GTotal (subst' s t)
      | Comp ct -> mk_Comp(subst_comp_typ' s ct)


let subst_binder' s (x, imp) = {x with sort=subst' s x.sort}, imp
let subst_binders' s bs = 
    bs |> List.mapi (fun i b -> 
        if i=0 then subst_binder' s b
        else subst_binder' (shift_subst i s) b)
let subst_arg' s (t, imp) = (subst' s t, imp)
let subst_args' s = List.map (subst_arg' s)
let subst_pat' s p : (pat * int) = 
    let rec aux n p : (pat * int) = match p.v with 
      | Pat_disj [] -> failwith "Impossible: empty disjunction"
     
      | Pat_constant _ -> p, n

      | Pat_disj(p::ps) -> 
        let p, m = aux n p in
        let ps = List.map (fun p -> fst (aux n p)) ps in
        {p with v=Pat_disj(p::ps)}, m

      | Pat_cons(fv, pats) ->
        let pats, n = pats |> List.fold_left (fun (pats, n) (p, imp) -> 
            let p, m = aux n p in
            ((p,imp)::pats, m)) ([], n) in
        {p with v=Pat_cons(fv, List.rev pats)}, n

      | Pat_var x ->
        let s = shift_subst n s in 
        let x = {x with sort=subst' s x.sort} in
        {p with v=Pat_var x}, n + 1

      | Pat_wild x -> 
        let s = shift_subst n s in 
        let x = {x with sort=subst' s x.sort} in
        {p with v=Pat_wild x}, n + 1 //these may be in scope in the inferred types of other terms, so shift the index

      | Pat_dot_term(x, t0) -> 
        let s = shift_subst n s in
        let x = {x with sort=subst' s x.sort} in
        let t0 = subst' s t0 in 
        {p with v=Pat_dot_term(x, t0)}, n //these are not in scope, so don't shift the index
  in aux 0 p

let push_subst_lcomp s lopt = match lopt with 
    | None 
    | Some (Inr _) -> lopt
    | Some (Inl l) -> 
      Some (Inl ({l with res_typ=subst' s l.res_typ;
                         comp=(fun () -> subst_comp' s (l.comp()))}))

let push_subst (s:subst_ts) t = 
//    let n = List.length s in
    match t.n with 
        | Tm_delayed _ -> failwith "Impossible"

        | Tm_constant _
        | Tm_fvar _
        | Tm_unknown 
        | Tm_uvar _ -> t

        | Tm_type _
        | Tm_bvar _ 
        | Tm_name _  -> subst' s t

        | Tm_uinst(t', us) -> 
          //t' must be an fvar---it cannot be substituted
          //but the universes may be substituted
          let us = List.map (subst_univ s) us in
          mk_Tm_uinst t' us

        | Tm_app(t0, args) -> mk (Tm_app(subst' s t0, subst_args' s args)) None t.pos

        | Tm_ascribed(t0, Inl t1, lopt) -> mk (Tm_ascribed(subst' s t0, Inl (subst' s t1), lopt)) None t.pos
        | Tm_ascribed(t0, Inr c, lopt) -> mk (Tm_ascribed(subst' s t0, Inr (subst_comp' s c), lopt)) None t.pos
       
        | Tm_abs(bs, body, lopt) -> 
          let n = List.length bs in 
          let s' = shift_subst n s in
          mk (Tm_abs(subst_binders' s bs, subst' s' body, push_subst_lcomp s' lopt)) None t.pos   
          
        | Tm_arrow(bs, comp) -> 
          let n = List.length bs in 
          mk (Tm_arrow(subst_binders' s bs, subst_comp' (shift_subst n s) comp)) None t.pos   
        
        | Tm_refine(x, phi) -> 
          let x = {x with sort=subst' s x.sort} in
          let phi = subst' (shift_subst 1 s) phi in
          mk (Tm_refine(x, phi)) None t.pos

        | Tm_match(t0, pats) -> 
          let t0 = subst' s t0 in
          let pats = pats |> List.map (fun (pat, wopt, branch) -> 
            let pat, n = subst_pat' s pat in 
            let s = shift_subst n s in 
            let wopt = match wopt with 
                | None -> None
                | Some w -> Some (subst' s w) in
            let branch = subst' s branch in 
            (pat, wopt, branch)) in
          mk (Tm_match(t0, pats)) None t.pos    
           
        | Tm_let((is_rec, lbs), body) -> 
          let n = List.length lbs in
          let sn = shift_subst n s in
          let body = subst' sn body in 
          let lbs = lbs |> List.map (fun lb -> 
            let lbt = subst' s lb.lbtyp in
            let lbd = if is_rec && Util.is_left (lb.lbname) //if it is a recursive local let, then all the let bound names are in scope for the body
                      then subst' sn lb.lbdef 
                      else subst' s lb.lbdef in
            let lbname = match lb.lbname with 
                | Inl x -> Inl ({x with sort=lbt})
                | Inr fv -> Inr ({fv with fv_name={fv.fv_name with ty=lbt}}) in
            {lb with lbname=lbname; lbtyp=lbt; lbdef=lbd}) in
          mk (Tm_let((is_rec, lbs), body)) None t.pos  
         
        | Tm_meta(t0, Meta_pattern ps) -> 
          mk (Tm_meta(subst' s t0, Meta_pattern (ps |> List.map (subst_args' s)))) None t.pos

        | Tm_meta(t, m) -> 
          mk (Tm_meta(subst' s t,  m)) None t.pos 

//EXTERNAL API
let rec compress (t:term) = 
    let t = force_delayed_thunk t in
    match t.n with
        | Tm_delayed(Inl(t, s), memo) -> 
          let t' = compress (push_subst s t) in
          Unionfind.update_in_tx memo (Some t');
//          memo := Some t';
          t'
        | _ -> force_uvar t

let rename s t = subst' [Renaming s] t
let rename_comp s c = subst_comp' [Renaming s] c

let subst (s:subst_t) (t:term) = subst' [s] t
let subst_comp s t = subst_comp' [s] t

let closing_subst bs = 
    List.fold_right (fun (x, _) (subst, n)  -> (Name2Index(x, n)::subst, n+1)) bs ([], 0) |> fst 
let open_binders' bs = 
   let rec aux bs (o:renaming) = match bs with
        | [] -> [], o
        | (x, imp)::bs' -> 
          let x' = {freshen_bv x with sort=rename o x.sort} in
          let o = 
            let o' = shift_renaming 1 o in 
            Index2Name(0, x')::o' in
          let bs', o = aux bs' o in 
          (x',imp)::bs', o in
   aux bs [] 
let open_binders (bs:binders) = fst (open_binders' bs)
let open_term' (bs:binders) t : binders * term * subst_t = 
   let bs', opening = open_binders' bs in
   bs', rename opening t, Renaming opening
let open_term (bs:binders) t = 
   let b, t, _ = open_term' bs t in 
   b, t
let open_comp (bs:binders) t = 
   let bs', opening = open_binders' bs in
   bs', rename_comp opening t

let open_pat (p:pat) = // pat * subst_t =
    let rec aux_disj (sub:renaming) pat_var_renaming p = 
        match p.v with 
           | Pat_disj _ -> failwith "impossible"

           | Pat_constant _ -> p

           | Pat_cons(fv, pats) ->
             {p with v=Pat_cons(fv, pats |> List.map (fun (p, b) -> 
                       aux_disj sub pat_var_renaming p, b))}

           | Pat_var x ->
             let yopt = Util.find_map pat_var_renaming (function 
                    | (x', y) when (x.ppname.idText=x'.ppname.idText) -> Some y
                    | _ -> None) in
             let y = match yopt with 
                | None -> {freshen_bv x with sort=rename sub x.sort} 
                | Some y -> y in
             {p with v=Pat_var y}

           | Pat_wild x -> 
             let x' = {freshen_bv x with sort=rename sub x.sort} in
             {p with v=Pat_wild x'}

           | Pat_dot_term(x, t0) -> 
             let x = {x with sort=rename sub x.sort} in
             let t0 = rename sub t0 in
             {p with v=Pat_dot_term(x, t0)} in 
    
    let rec aux (sub:renaming) pat_var_renaming p = match p.v with 
       | Pat_disj [] -> failwith "Impossible: empty disjunction"
     
       | Pat_constant _ -> p, sub, pat_var_renaming
       
       | Pat_disj(p::ps) -> 
         let p, sub, renaming = aux sub pat_var_renaming p in
         let ps = List.map (aux_disj sub renaming) ps in
         {p with v=Pat_disj(p::ps)}, sub, renaming

       | Pat_cons(fv, pats) ->
         let pats, sub, renaming = pats |> List.fold_left (fun (pats, sub, renaming) (p, imp) -> 
             let p, sub, renaming = aux sub renaming p in
             ((p,imp)::pats, sub, renaming)) ([], sub, pat_var_renaming) in
         {p with v=Pat_cons(fv, List.rev pats)}, sub, renaming

       | Pat_var x ->
         let x' = {freshen_bv x with sort=rename sub x.sort} in
         let sub = 
            let sub' = shift_renaming 1 sub in 
            Index2Name(0, x')::sub' in
         {p with v=Pat_var x'}, sub, (x,x')::pat_var_renaming

       | Pat_wild x -> 
         let x' = {freshen_bv x with sort=rename sub x.sort} in
         let sub = 
            let sub' = shift_renaming 1 sub in 
            Index2Name(0, x')::sub' in
         {p with v=Pat_wild x'}, sub, (x,x')::pat_var_renaming

       | Pat_dot_term(x, t0) -> 
         let x = {x with sort=rename sub x.sort} in
         let t0 = rename sub t0 in
         {p with v=Pat_dot_term(x, t0)}, sub, pat_var_renaming in //these are not in scope, so don't shift the index
    
    let p, sub, _ = aux [] [] p in
    p, sub

let open_branch (p, wopt, e) = 
    let p, opening = open_pat p in
    let wopt = match wopt with 
        | None -> None
        | Some w -> Some (rename opening w) in
    let e = rename opening e in 
    (p, wopt, e)
    
let close (bs:binders) t = rename (closing_subst bs) t
let close_comp (bs:binders) (c:comp) = rename_comp (closing_subst bs) c
let close_binders (bs:binders) : binders =
    let rec aux (s:renaming) (bs:binders) = match bs with 
        | [] -> []
        | (x, imp)::tl ->  
          let x = {x with sort=rename s x.sort} in 
          let s' = Name2Index(x, 0)::shift_renaming 1 s in
          (x, imp)::aux s' tl in
    aux [] bs

let close_lcomp (bs:binders) lc = 
    let s = closing_subst bs in 
    {lc with res_typ=rename s lc.res_typ;
             comp=(fun () -> rename_comp s (lc.comp())); }

let close_pat p = 
    let rec aux (sub:renaming) p = match p.v with
       | Pat_disj [] -> failwith "Impossible: empty disjunction"
     
       | Pat_constant _ -> p, sub
       
       | Pat_disj(p::ps) -> 
         let p, sub = aux sub p in
         let ps = List.map (fun p -> fst (aux sub p)) ps in
         {p with v=Pat_disj(p::ps)}, sub

       | Pat_cons(fv, pats) ->
         let pats, sub = pats |> List.fold_left (fun (pats, sub) (p, imp) -> 
             let p, sub = aux sub p in
             ((p,imp)::pats, sub)) ([], sub) in
         {p with v=Pat_cons(fv, List.rev pats)}, sub

       | Pat_var x ->
         let x = {x with sort=rename sub x.sort} in
         let sub = Name2Index(x, 0)::shift_renaming 1 sub in 
         {p with v=Pat_var x}, sub

       | Pat_wild x -> 
         let x = {x with sort=rename sub x.sort} in
         let sub = Name2Index(x, 0)::shift_renaming 1 sub in 
         {p with v=Pat_wild x}, sub

       | Pat_dot_term(x, t0) -> 
         let x = {x with sort=rename sub x.sort} in
         let t0 = rename sub t0 in
         {p with v=Pat_dot_term(x, t0)}, sub in //these are not in scope, so don't shift the index    
    aux [] p

let close_branch (p, wopt, e) = 
    let p, closing = close_pat p in 
    let wopt = match wopt with
        | None -> None
        | Some w -> Some (rename closing w) in
    let e = rename closing e in
    (p, wopt, e)

let univ_var_opening (us:univ_names) = 
    let n = List.length us - 1 in
    let s, us' = us |> List.mapi (fun i u -> 
        let u' = Syntax.new_univ_name (Some u.idRange) in
        UIndex2UName(n - i, u'), u') |> List.unzip in
    s, us'

let open_univ_vars  (us:univ_names) (t:term)  : univ_names * term = 
    let s, us' = univ_var_opening us in 
    let t = rename s t in
    us', t

let open_univ_vars_comp (us:univ_names) (c:comp) : univ_names * comp = 
    let s, us' = univ_var_opening us in 
    us', rename_comp s c

let close_univ_vars (us:univ_names) (t:term) : term = 
    let n = List.length us - 1 in
    let s = us |> List.mapi (fun i u -> UName2UIndex(u, n - i)) in
    rename s t

let close_univ_vars_comp (us:univ_names) (c:comp) : comp = 
    let n = List.length us - 1 in
    let s = us |> List.mapi (fun i u -> UName2UIndex(u, n - i)) in
    rename_comp s c

let open_let_rec lbs (t:term) =
    if is_top_level lbs then lbs, t //top-level let recs are not opened
    else (* Consider
                let rec f<u> x = g x
                and g<u'> y = f y in
                f 0, g 0
            In de Bruijn notation, this is
                let rec f x = g@1 x@0
                and g y = f@2 y@0 in
                f@1 0, g@0 0
            i.e., the recursive environment for f is, in order:
                        u, f, g, x 
                  for g is
                        u, f, g, y 
                  and for the body is
                        f, g
         *)
         let n_let_recs, lbs, let_rec_opening = 
             List.fold_right (fun lb (i, lbs, out) -> 
                let x = Syntax.freshen_bv (left lb.lbname) in
                i+1, {lb with lbname=Inl x}::lbs, Index2Name(i, x)::out) lbs (0, [], []) in

         let lbs = lbs |> List.map (fun lb -> 
              let _, us, u_let_rec_opening = 
                  List.fold_right (fun u (i, us, out) -> 
                    let u = Syntax.new_univ_name None in
                    i+1, u::us, UIndex2UName(i, u)::out)
                  lb.lbunivs (n_let_recs, [], let_rec_opening) in
             {lb with lbunivs=us; lbdef=rename u_let_rec_opening lb.lbdef}) in

         let t = rename let_rec_opening t in 
         lbs, t

let close_let_rec lbs (t:term) = 
    if is_top_level lbs then lbs, t //top-level let recs do not have to be closed
    else let n_let_recs, let_rec_closing = 
            List.fold_right (fun lb (i, out) -> i+1, Name2Index(left lb.lbname, i)::out) lbs (0, []) in
         let lbs = lbs |> List.map (fun lb ->
                let _, u_let_rec_closing = List.fold_right (fun u (i, out) -> i+1, UName2UIndex(u, i)::out) lb.lbunivs (n_let_recs, let_rec_closing) in
                {lb with lbdef=rename u_let_rec_closing lb.lbdef}) in
         let t = rename let_rec_closing t in 
         lbs, t

let close_tscheme (binders:binders) ((us, t) : tscheme) = 
    let n = List.length binders - 1 in
    let k = List.length us in 
    let s = List.mapi (fun i (x, _) -> Name2Index(x, k + (n - i))) binders in
    let t = rename s t in 
    (us, t)

let close_univ_vars_tscheme (us:univ_names) ((us', t):tscheme) = 
   let n  = List.length us - 1 in
   let k = List.length us' in
   let s = List.mapi (fun i x -> UName2UIndex(x, k + (n - i))) us in
   (us', rename s t)

let opening_of_binders (bs:binders) : subst_t = 
  let n = List.length bs - 1 in
  Renaming (bs |> List.mapi (fun i (x, _) -> Index2Name(n - i, x)))
