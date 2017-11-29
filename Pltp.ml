(* ************************************************************************** *)
(*                                                                            *)
(* A fully automatic inductive theorem prover for a logic based on Pure Lisp. *)
(* Modeled on the original Boyer-Moore prover presented in Moore's PhD, 1973. *)
(*                                                                            *)
(* Authored by Grant Olney Passmore,                                          *)
(* Aesthetic Integration, Ltd, and Clare Hall, University of Cambridge.       *)
(* (c)Copyright Aesthetic Integration, Ltd, 2014.  All rights reserved.       *)
(*                                                                            *)
(* Contact: grant.passmore@cl.cam.ac.uk -or- http://www.cl.cam.ac.uk/~gp351/. *)
(*                                                                            *)
(* ************************************************************************** *)

open Printf
open String
open Format

type expr =
    Nil
  | Cons of expr * expr
  | Car of expr
  | Cdr of expr
  | Cond of expr * expr * expr
  | Equal of expr * expr
  | Const of string
  | Var of string
  | Abv of string
  | FertTm of string * expr
  | FunCall of string * expr list

(* Pretty-print expressions *)

let rec pp_expr ppf x =
  let f = pp_expr in
  let rec pp_list fu ppf xs =
    match xs with
      [] -> ()
    | [x] -> fu ppf x
    | x::xs -> fprintf ppf "%a@;<1 0>%a" fu x (pp_list fu) xs
  in
  match x with
    Nil -> fprintf ppf "NIL"
  | Cons (Nil, Nil) -> fprintf ppf "T"
  | Cons (a,b) -> fprintf ppf "@[(CONS @[@[%a@]@;<1 0>@[%a@]@])@]" f a f b
  | Car a -> fprintf ppf "@[(CAR %a)@]" f a
  | Cdr a -> fprintf ppf "@[(CDR %a)@]" f a
  | Cond (a,b,c) ->
     fprintf ppf "@[(COND @[@[%a@]@;<1 0>@[%a@]@;<1 0>@[%a@]@])@]" f a f b f c
  | Equal (a,b) ->
     fprintf ppf "@[(EQUAL @[@[%a@]@;<1 0>@[%a@]@])@]" f a f b
  | Const s -> fprintf ppf "%s" (capitalize s)
  | Var s -> fprintf ppf "%s" (capitalize s)
  | Abv s -> fprintf ppf "%s" (capitalize s)
  | FertTm (s, _) -> fprintf ppf "(*%s)" (capitalize s)
  | FunCall (f, args) ->
     fprintf ppf "@[(%s @[%a@])@]"
             (capitalize f)
             (pp_list pp_expr) args

let print_expr =
  fprintf std_formatter "@.";
  pp_expr std_formatter

(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
(*  Function definitions                                                     *)
(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)

(* Note that the `define' function (used to define functions and
   record them in the defs global) is given later, as it relies upon
   the `normalation' machinery, which itself relies upon `eval,'
   `normalize' and `reduce.' *)

type def = { fun_name : string;
             fun_args : string list;
             fun_body : expr;
             (* props: (non-)boolean, (non-)numeric, (non-)recursive *)
             fun_props : (string list) ref;
             (* type: Name of the fn's typeexpr, if it is defined. *)
             fun_type : (string option) ref}

(* Global containing all defined functions *)

let defs = ref []

let get_def f =
  let rec get_def' (f, ds) =
    match ds with
      [] -> raise (Failure (sprintf "Undeclared function: %s" f))
    | (d::ds) -> if d.fun_name = f then d
                 else get_def' (f, ds) in
  get_def' (f, (!defs))

let pp_def ppf d =
  fprintf ppf "@.@[(%s (LAMBDA @[(%s)@;<1 0>@[%a@]@]))@]@."
          d.fun_name
          (concat " " d.fun_args)
          pp_expr d.fun_body

let print_def d =
  pp_def std_formatter d;
  let d_props = !(d.fun_props) in
  if d_props <> [] then
    fprintf std_formatter "@. * Properties: [%s].@."
            (String.concat "; " !(d.fun_props))

let show_def x = print_def (get_def x)

let div =
  "---------------------------------------"
  ^ "----------------------------------------"

let show_defs () =
  let f = std_formatter in
  fprintf f "%s@.- Defined functions:@.%s@." div div;
  List.iter (fun d -> print_def d; fprintf f "@.%s@." div)
            (List.fast_sort (fun d d' -> String.compare d.fun_name d'.fun_name)
                            (!defs))

let has_prop d p = List.mem p !(d.fun_props)

let set_prop d p =
  d.fun_props := p :: !(d.fun_props);;

let unset_prop d p =
  d.fun_props := List.filter (fun x -> x <> p) !(d.fun_props)

(* Is a function definition recursive? Note we don't yet support
   the detection of mutual recursion. *)

let is_rec d =
  if has_prop d "recursive" then
    true
  else
    let rec is_rec' fn fb =
      let r = is_rec' fn in
      match fb with
        Cond (a,b,c) -> r a || r b || r c
      | Car a -> r a
      | Cdr a -> r a
      | Cons (a,b) -> r a || r b
      | Equal (a,b) -> r a || r b
      | FunCall (f, args) ->
         f = fn || List.exists r args
      | _ -> false
    in
    let r = is_rec' d.fun_name d.fun_body
    in
    if r then set_prop d "recursive" else ();
    r

(* Abbreviations, including a CONS encoding of natural numbers *)

type abv = { abv_name : string;
             abv_val : expr }

let abvs = [ {abv_name = "T"; abv_val = Cons (Nil, Nil)} ]

let rec encode_nat n =
  if n < 0 then raise (Failure "Cannot CONS-encode a negative integer")
  else
    match n with
      0 -> Nil
    | _ -> Cons (Nil, encode_nat (n-1))

let expand_abv s =
  try
    let i = int_of_string s
    in encode_nat i
  with
    _ -> let a = List.find (fun x -> x.abv_name = s) abvs in
         a.abv_val

let rec expand_abvs e =
  let f = expand_abvs in
  match e with
    Car a -> Car (f a)
  | Cdr a -> Cdr (f a)
  | Cons (a, b) ->
     let e1, e2 = f a, f b in
     Cons (e1, e2)
  | Cond (a,b,c) ->
     let e1, e2, e3 = f a, f b, f c in
     Cond (e1, e2, e3)
  | Equal (a, b) ->
     let e1, e2 = f a, f b in
     Equal (e1, e2)
  | FunCall (s, args) ->
     let args' = List.map expand_abvs args in
     FunCall (s, args')
  | Abv a -> expand_abv a
  | _ -> e

(* Two built-in type functions: boolean and numeric *)

let rec boolean e =
  match expand_abvs e with
    Nil -> true
  | Cons (Nil, Nil) -> true (* T *)
  | Equal (a,b) -> true
  | Cond (a,b,c) -> boolean b && boolean c
  | FunCall (f, args) ->
     (try
         let d = get_def f in
         if has_prop d "boolean" then true
         else if has_prop d "non-boolean" then false
         else
           begin
             set_prop d "boolean";
             if boolean d.fun_body then
               true
             else
               (unset_prop d "boolean";
                set_prop d "non-boolean";
                false)
           end
       with _ ->
         (* Function not defined yet, e.g., during a definition event. *)
         false)
  (* Fertilization terms are always boolean *)
  | FertTm _ -> true
  | _ -> false

let rec numeric e =
  match expand_abvs e with
    Nil -> true (* 0 *)
  | Cons (Nil, b) -> numeric b (* b + 1 *)
  | Equal (a,b) -> true (* 0 or 1 *)
  | Cond (a,b,c) -> numeric b && numeric c
  | FunCall (f, args) ->
     (try
         let d = get_def f in
         if has_prop d "numeric" then true
         else if has_prop d "non-numeric" then false
         else
           begin
             set_prop d "numeric";
             if numeric d.fun_body then
               true
             else
               (unset_prop d "numeric";
                set_prop d "non-numeric";
                false)
           end
       with _ ->
         (* Function not defined yet, e.g., during a definition event. *)
         false)
  | _ -> false

(* Explicit and specific lists *)

let explicit_list l =
  match l with
    Nil -> true
  | Cons _ -> true
  | _ -> false

let rec specific_list l =
  match l with
    Nil -> true
  | Cons (x, y) -> specific_list (expand_abvs x)
                   && specific_list (expand_abvs y)
  | _ -> false

(* Is x an explicit sublist of y?
   Note this check is non-proper (i.e., it is reflexive) *)

let rec explicit_sublist (x,y) =
  if x = y then true
  else
    match y with
      Nil -> false
    | Cons (a, b) ->
       explicit_sublist (x, a) || explicit_sublist (x, b)
    | _ -> false

(* Ident: Check for equality modulo abbreviations.  Relies on the
    theorem that no list is equal to one of its proper sublists. *)

type id_judgement = Id_Equal | Id_Unequal | Id_Unknown

let rec ident (e1, e2) =
  let e1', e2' = expand_abvs e1, expand_abvs e2 in
  if e1' = e2' then Id_Equal else
    match e1', e2' with
      Cons _, Nil -> Id_Unequal
    | Nil, Cons _ -> Id_Unequal
    | Cons _, _
    | _, Cons _ ->
       (* Note: In the current branch, we know that e1' <> e2' *)
       if specific_list e1' && specific_list e2' then Id_Unequal
       else if explicit_sublist (e1', e2') || explicit_sublist (e2', e1')
       then Id_Unequal
       else Id_Unknown
    | _ -> Id_Unknown

(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
(*  Evaluation                                                               *)
(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)

(* Evaluation with support for Skolem constants and fault analysis *)
(* Eval produces both an output expression and fault analysis data *)
(* which is used to construct instances of an induction scheme.    *)

type binding = string * expr

type state = { var_bindings  : binding list;
               watched_funs  : string list;
               rec_arg_eval  : bool;

               (* cfc: deepest recursive function body undergoing
                       expansion *)

               cur_fun_call  : (expr * (binding list)) option;

               (* fd: are we in the midst of normalating a function
                  body at definition time? If so, we give (Some
                  fun_name), where fun_name is the name of the
                  function being defined. *)

               fun_def       : string option }

type pocket = expr list

type bomb_lst = pocket list

type fault = { bomb_lst : bomb_lst;
               failures : expr list }

let cur_pocket = ref []

let cur_fault = ref { bomb_lst = [];
                      failures = [] }

let close_pocket () =
  if !cur_pocket <> [] then
    cur_fault := {!cur_fault with
                   bomb_lst = (!cur_pocket) :: (!cur_fault).bomb_lst};
  cur_pocket := []

type analysis = { mutable faults : fault list;
                  mutable fault_evals : ((expr * (binding list)) option) list }

let analysis = { faults = [];
                 fault_evals = [] }

let clr_analysis () =
  analysis.faults <- [];
  analysis.fault_evals <- [];
  cur_pocket := [];
  cur_fault := { bomb_lst = []; failures = [] }

let close_fault () =
  if not(!cur_fault.bomb_lst = [] && !cur_fault.failures = []) then
    analysis.faults <- (!cur_fault) :: analysis.faults;
  cur_fault := { bomb_lst = []; failures = [] }

let record_fault (x, state) =
  if state.rec_arg_eval then
    let _ = if not(List.mem state.cur_fun_call analysis.fault_evals)
            then analysis.fault_evals <-
                   state.cur_fun_call :: analysis.fault_evals
            else () in
    cur_pocket := x :: (!cur_pocket)
  else
    cur_fault := { (!cur_fault) with
                   failures = x :: ((!cur_fault).failures) };
  x

let pp_bindings ppf bs =
  List.map (fun (v, e) ->
            fprintf ppf "(%s, %a)" v pp_expr e)
           bs

(* Evaluation, with Skolem constants and failure analysis  *)

let rec eval' (e, state) =
  match e with
    Abv v -> expand_abv v
  | Car x ->
    let x' = eval' (x, state) in
    (match x' with
       Cons (a, b) -> a
     | Nil -> Nil
     | _ -> record_fault (Car x', state))
  | Cdr x ->
     let x' = eval' (x, state) in
     (match x' with
        Cons (a, b) -> b
      | Nil -> Nil
      | _ -> record_fault (Cdr x', state))
  | Cons (x, y) ->
     let x', y' = eval' (x, state), eval' (y, state) in Cons (x', y')
  | Cond (x, y, z) ->
     let x' = eval'(x, state) in
     (match ident (x', Nil) with
        Id_Equal -> eval' (z, state)
      | Id_Unequal -> eval' (y, state)
      | Id_Unknown -> Cond (x', eval' (y, state), eval' (z, state)))
  | Equal (x, y) ->
     let x', y' = eval'(x, state), eval'(y, state) in
     (match ident (x', y') with
        Id_Equal -> Cons (Nil, Nil) (* T *)
      | Id_Unequal -> Nil
      | Id_Unknown ->
         (match x', y' with
            Cons (a,b), Cons (c,d) ->
            eval' (Cond (Equal (a,c), Equal (b,d), Nil), state)
           | _ -> Equal (x', y')))
  | Var v ->
     (try List.assoc v state.var_bindings
      with _ ->
        (match state.fun_def with

         (* If we're not in a function definition event, then
            having an unbound variable is an error. *)

         | None -> raise (Failure (sprintf "Unbound variable: %s" v))

         (* Else, we're normalating a function body at definition time,
            and we just return the unbound variable as-is. *)
         | _ -> Var v))

  (* Non-primitive function evaluation *)

  | FunCall (f, args) ->

     (* Note that eval is used in two ways by the prover:
         (i) During function definition events, and
        (ii) During theorem proving.

        For (i): Given a function definition event defining function
        fun_name, the body of fun_name must be normalated before it is
        stored in the defs global. In this case, state.fun_def is set
        to the value (Some fun_name). Then, if the body of function
        fun_name calls fun_name recursively, we want to just return
        this function call with its args eval'd. We check for this
        case first below.

        Otherwise, if this FunCall(f, _) is not s.t. (state.fun_def =
        Some f), e.g. we're in eval use (ii), then we proceed as usual
        with function evaluation (with support for Skolem constants
        and fault analysis). *)

     if (match state.fun_def with Some g when g = f -> true | _ -> false)
     then
       let args' = List.map (fun x -> eval' (x, state)) args in
       FunCall (f, args')
     else
     let rec_f_call = List.mem f state.watched_funs in
     let rec_arg_eval = (* state.rec_arg_eval || *) rec_f_call in
     let state = { state with rec_arg_eval = rec_arg_eval } in
     let args' = List.map (fun x -> eval' (x, state)) args in
     let d = get_def f in
     let f_is_rec = is_rec d in
     let b = List.combine d.fun_args args' in
     let state' = { state with var_bindings = b @ state.var_bindings;
                               watched_funs = f :: state.watched_funs }
     in

     (* Evaluating function f when all its args are specific lists.   *)

     if (List.for_all specific_list args') then
       eval' (d.fun_body, state')
     else
       let arg_failure = List.mem state.cur_fun_call analysis.fault_evals in

       (* Evaluating function f when its args contain Skolem constants. *)

       if (arg_failure (* && rec_f_call *)) then

         (* Failures have occurred in evaluating the arguments, and
            the input expression e is a recursive call of a function
            being evaluated. So, we return e with its args eval'd. *)

         (close_pocket ();
          FunCall (f, args'))
       else

         (* Is f (i) the first function expansion,
                (ii) under an ongoing f-expansion (a recursive call), or
               (iii) recursive and the first f-expansion in the context?
            If so, make f's body with eval'd args the new cfc. *)

         let cfc = if rec_f_call || f_is_rec || state.cur_fun_call = None
                   then Some (d.fun_body, state'.var_bindings)
                   else state.cur_fun_call in
         let f' = eval' (d.fun_body, { state' with cur_fun_call = cfc;
                                                   rec_arg_eval = false }) in
         let body_failure = List.mem cfc analysis.fault_evals in
         if body_failure then
           (close_fault ();
            FunCall (f, args'))
         else f'
  | _ -> e

(* Top-level eval function *)

let eval ?(fun_def=None) x =
  let s = { var_bindings = [];
            watched_funs = [];
            rec_arg_eval = false;
            cur_fun_call = None;
            fun_def = fun_def } in
  begin
    clr_analysis ();
    eval' (x, s)
  end

(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
(*  Normalization                                                            *)
(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)

let rec normalize e =
  let nm = normalize in
  match expand_abvs e with
    Equal (x,y) ->
    let x',y' = nm x, nm y in
    (match ident(x',y') with
       Id_Equal -> Cons (Nil, Nil) (* T *)
     | Id_Unequal -> Nil
     | Id_Unknown ->

        (* Equal (x, T) -> x, if x is boolean *)

        if y' = Cons(Nil, Nil) && boolean x' then x'
        else if x' = Cons(Nil, Nil) && boolean y' then y'
        else
          (match x' with

             (* e is Equal(Equal(a, b), y') *)

             Equal(a, b) -> nm (Cond (Equal (a, b),
                                      Equal (y', Cons (Nil, Nil) (* T *)),
                                      Cond (y', Nil, Cons (Nil, Nil) (* T *))))
           | _ -> (match y' with

                     (* e is Equal(x', Equal(a, b)) *)

                     Equal (a, b) -> nm (Cond (Equal (a, b),
                                               Equal (x', Cons (Nil, Nil) (* T *)),
                                               Cond (x', Nil, Cons (Nil, Nil) (* T *))))
                   | _ ->

                      (* Equal (x1, Cond(a,b,c)) -> Cond(a, Equal(x1, b), Equal(x1, c) *)

                      (match x', y' with
                         x1, Cond(a,b,c) -> nm (Cond(a, Equal(x1, b), Equal(x1, c)))
                       | Cond(a,b,c), x1 -> nm (Cond(a, Equal(b, x1), Equal(c, x1)))
                       | _ -> Equal (x', y')))))
  | Cond (a, b, c) ->
     let a' = nm a in
     (match ident(a', Nil) with
        Id_Equal -> nm c
      | Id_Unequal -> nm b
      | Id_Unknown ->
         let b', c' = nm b, nm c in
         (match ident(b', Abv "T"), ident(c', Nil) with
            Id_Equal, Id_Equal
               when boolean a' -> a'
          | _ ->

             (* Cond (x, y, y) -> y *)

             if b' = c' then b'
               (* Cond (x, x, Nil) -> x *)
             else if a' = b' && c' = Nil then a'
             else

               (* Cond(Cond(x,y,z),u,v) -> Cond(x,Cond(y,u,v),Cond(z,u,v))
                  where either (i) y or z is Nil, (ii) u and v non-Nil. *)

               (match a' with
                  Cond(x, y, z) ->
                  if (y = Nil || z = Nil) || (b' <> Nil && c' <> Nil)
                  then nm (Cond(x, Cond(y, b', c'), Cond(z, b', c')))
                  else Cond(a', b', c')
                | _ ->
                    Cond(a', b', c'))))
  | Cons (x,y) ->
     let x',y' = nm x, nm y in

     (* Cons(Cond(a,b,c),y) --> Cond(a,Cons(b,y),Cons(c,y)) *)

     (match x',y' with
        Cond(a,b,c),d -> nm (Cond(a,Cons(b,d),Cons(c,d)))
      | d,Cond(a,b,c) -> nm (Cond(a,Cons(d,b),Cons(d,c)))
      | _ -> Cons (x',y'))
  | Car x ->
     let x' = nm x in

     (* Car(Cond(a,b,c)) --> Cond(a,Car(b),Car(c)) *)

     (match x' with
        Cond(a,b,c) -> nm (Cond(a, Car b, Car c))
      | _ -> Car x')
  | Cdr x ->
     let x' = nm x in

     (* Cdr(Cond(a,b,c)) --> Cond(a,Cdr(b),Cdr(c)) *)

     (match x' with
        Cond(a,b,c) -> nm (Cond(a, Cdr b, Cdr c))
      | _ -> Cdr x')
  | FunCall(f, args) ->
     let args' = List.map normalize args in

     (* f( x1 ... Cond (y, u, v) ... xn )
          --> Cond(y, f(x1, ..., u, ..., xn), f(x1, ..., v, ..., xn)). *)

     let rec cond_pos xs i =
       (match xs with
          [] -> None
        | ((Cond (a,b,c)) :: _) -> Some (i, Cond (a,b,c))
        | _ :: xs -> cond_pos xs (i+1)) in
     let rec new_args k x rst =
         (match rst with
            [] -> []
          | r :: rst ->
             if k <= 0 then (x :: rst) else
               r :: (new_args (k-1) x rst)) in
     let i = cond_pos args' 0 in
     (match i with
        Some (n, c) ->
        let new_f x = FunCall(f, new_args n x args') in
        (match c with
           Cond(y, u, v) -> nm (Cond(y, new_f u, new_f v))
         | _ -> FunCall(f, args'))
      | None -> FunCall(f, args'))
  | _ -> e

(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
(*  Reduction                                                                *)
(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)

let rec subst e a b =
  let s x = subst x a b in
  if e = a then b else
    match e with
      Car x -> Car (s x)
    | Cdr x -> Cdr (s x)
    | Cons (x,y) -> Cons (s x, s y)
    | Cond (x,y,z) -> Cond (s x, s y, s z)
    | Equal (x,y) -> Equal (s x, s y)
    | FunCall (f, args) ->
       let args' = List.map s args in
       FunCall (f, args')
    | _ -> e

let rec reduce' asms z =
  let rd = reduce' asms in
  match z with
    Car x -> Car (rd x)
  | Cdr x -> Cdr (rd x)
  | Cons (x,y) -> Cons (rd x, rd y)
  | FunCall (f, args) ->
     let args' = List.map rd args in
     FunCall(f, args')
  | Cond (x,p,q) ->
     let x, p, q =
       (match x with
          Cond _ -> rd x, rd p, rd q
        | _ -> x, p, q) in
     if List.mem x asms then rd p
     else if x = Nil then rd q
     else
       (match x with
          Cons _ -> rd p
        | x when not(boolean x) ->
           let tb = reduce' (x::asms) p in
           let fb = reduce' asms (subst q x Nil) in
           Cond (x, tb, fb)
        | Equal (u,v) when specific_list v ->
           let r = subst p u v in
           Cond (Equal (u, v), rd r, rd (subst q x Nil))
        | x when boolean x ->
           let tb = rd (subst p x (Cons (Nil, Nil))) (* T *) in
           let fb = rd (subst q x Nil) in
           Cond (x, tb, fb)
        | _ -> Cond (rd x, rd p, rd q))
  | _ -> z

let reduce z = reduce' [] z

(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
(*  Normalation                                                              *)
(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)

let rec normalate ?(fun_def=None) ?(quiet=false) e =
  let diff x y = expand_abvs x <> expand_abvs y in
  let p = fprintf std_formatter in
  let e' = eval ~fun_def:fun_def e in
  let _ = if not(quiet) && diff e' e then
            p "@.@.Evaluation yields: @.@ @[%a@]" pp_expr e' in
  let e'' = normalize e' in
  let _ = if not(quiet) && diff e'' e' then
            p "@.@.Normalizes to: @.@ @[%a@]" pp_expr e'' in
  let e''' = reduce e'' in
  let _ = if not(quiet) && diff e''' e'' then
            p "@.@.Reduces to: @.@ @[%a@]" pp_expr e''' in
  if diff e e''' then normalate ~fun_def:fun_def e'''
  else e

(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
(*  Function definition                                                      *)
(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)

let define d =
  let d_name = capitalize d.fun_name in
  let _ = fprintf std_formatter "Defining %s..." d_name in
  let norm_body = normalate ~fun_def:(Some d_name) ~quiet:true (d.fun_body) in
  let d' = { d with fun_name = d_name; fun_body = norm_body } in
  defs := d' :: (!defs);
  (* Check for some basic properties, recording the result on d'.fun_props. *)
  let _ = is_rec d' in
  let f_call = FunCall(d'.fun_name, List.map (fun s -> Const s) d'.fun_args) in
  let _ = boolean f_call in
  let _ = numeric f_call in
  fprintf std_formatter "...Done@."

(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
(*  Fertilization                                                            *)
(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)

(* TODO: Treat a FertTm like Nil in the Cond simp rule. *)

(* Note: To `hide' a given negated equality NEGEQ, we create a FertTm
   of the form FertTm ("n", NEGEQ), with n a natural number not yet
   used to name a FertTm. *)

(* To do so, we keep track of how many FertTms have been created. *)

let num_fert_tms = ref 0

let new_fert_tm e =
  let i = !num_fert_tms in
  let _ = num_fert_tms := !num_fert_tms + 1 in
  FertTm (sprintf "%d" (i+1), e)

let rec occurs tm e =
  let o = occurs tm in
  if e=tm then true else
    match e with
      Car a -> o a
    | Cdr a -> o a
    | Cons (a, b) -> o a || o b
    | Cond (a, b, c) -> o a || o b
    | Equal (a, b) -> o a || o b
    | FunCall (_, args) -> List.exists o args
    | _ -> false

let rec fertilize' e =
  let f = fertilize' in
  let pp = fprintf std_formatter in
  match e with
    Cons (a, b) -> Cons (f a, f b)
  | Car a -> Car (f a)
  | Cdr a -> Car (f a)
  | Cond (Equal (x,y), Equal(p_1, p_2), z)
       when occurs y p_1 && occurs y p_2 && boolean z
            && not(occurs x p_1 || occurs x p_2) ->
     let ft = new_fert_tm (Cond (Equal (x,y), Nil, Abv "T")) in
     let _ = pp "@.Fertilize with %a.@." pp_expr (Equal (x,y)) in
     let p_2_x = subst p_2 y x in
     if ident(z, Abv "T") = Id_Equal then
       Cond(Equal(p_1, p_2_x), Abv "T", ft)
     else
       Cond (Cond (Equal(p_1, p_2_x), Abv "T", ft),
             Cond (z, Abv "T", Equal (x, y)), Nil)
  | Cond (Equal (x,y), p, z)
       when occurs y p && boolean p && boolean z ->
     let p_x = subst p y x in
     let ft = new_fert_tm (Cond (Equal (x,y), Nil, Abv "T")) in
     let _ = pp "@.Fertilize with %a.@." pp_expr (Equal (x,y)) in
     if ident(z, Abv "T") = Id_Equal then
       Cond (p_x, Abv "T", ft)
     else
       Cond (Cond (p_x, Abv "T", ft),
             Cond (z, Abv "T", Equal (x, y)), Nil)
  (* Symmetry - 17 *)
  | Cond (Equal (x,y), p, z)
       when occurs x p && boolean p && boolean z ->
     let p_y = subst p x y in
     let ft = new_fert_tm (Cond (Equal (x,y), Nil, Abv "T")) in
     let _ = pp "@.Fertilize with %a.@." pp_expr (Equal (x,y)) in
     if ident(z, Abv "T") = Id_Equal then
       Cond (p_y, Abv "T", ft)
     else
       Cond (Cond (p_y, Abv "T", ft),
             Cond (z, Abv "T", Equal (x, y)), Nil)
  | Cond (x,y,z) -> Cond (f x, f y, f z)
  | Equal (x,y) -> Equal (f x, f y)
  | _ -> e

let fertilize e =
  let _ = fprintf std_formatter "@." in
  let e' = fertilize' e in
  e'

(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
(*  Generalization                                                           *)
(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)

let num_gen_consts = ref 0

(* Type function generation *)

let rec type_expr e =
  if boolean e then
    FunCall("BOOLEAN", [Var "X"])
  else if numeric e then
    FunCall("NUMBERP", [Var "X"])
  else if specific_list e then
    Equal(Var "X", e)
  else
    match expand_abvs e with
      Car _ -> Abv "T"
    | Cdr _ -> Abv "T"
    | Cons (a,b) ->
       let t_a, t_b = type_expr a, type_expr b in
       let t_a' = subst t_a (Var "X") (Car (Var "X")) in
       let t_b' = subst t_b (Var "X") (Cdr (Var "X")) in
       Cond (Var "X", Cond (t_a', t_b', Nil), Nil)
    | Equal _ ->
       Cond (Var "X", Equal (Var "X", Abv "T"), Abv "T")
    | Cond (_, b, c) ->
       let t_b, t_c = type_expr b, type_expr c in
       Cond (t_b, Abv "T", t_c)
    | FunCall(f, args) ->
       let d = get_def f in
       (match !(d.fun_type) with
          Some g -> FunCall(g, [Var "X"])
        | None ->
           let ft_name = f ^ "_TYPE" in
           let _ = d.fun_type := Some ft_name in
           let b = d.fun_body in
           let ft_body = type_expr b in
           let ft_body' = subst ft_body (FunCall(ft_name, [Var "X"])) Nil in
           let ft_def = { fun_name = ft_name;
                          fun_args = ["X"];
                          fun_body = ft_body';
                          fun_props = ref [];
                          fun_type = ref None } in

           (* Note that define does automatic normalation of
              function bodies. *)
           let _ = define ft_def in
           FunCall(ft_name, [Var "X"]))
    | _ -> Abv "T"

module ExprSet = Set.Make
 (struct
   type t = expr
   let compare = Pervasives.compare
 end)

let expr_set l =
  let s = ref ExprSet.empty in
  let _ = List.iter (fun x -> s := ExprSet.add x (!s)) l in
  (!s)

let non_atoms_of_expr e =
  let out = ref (ExprSet.empty) in
  let add x = out := ExprSet.add x (!out) in
  let rec non_atoms_of_expr' e =
    let f = non_atoms_of_expr' in
    match e with
      Car a
    | Cdr a -> (add e; f a)
    | Cons (Nil, Nil) -> () (* T is treated as atomic *)
    | Cons (a,b) -> (add e; f a; f b)
    | Equal (a,b) -> (add e; f a; f b)
    | Cond (a,b,c) -> (add e; f a; f b; f c)
    | FunCall (_, args) ->
       let _ = add e in
       List.iter f args
    | _ -> ()
  in
  let _ = non_atoms_of_expr' e in
  (!out)

let rec gather_gen_tms' e =
  let union a b c = (ExprSet.union a (ExprSet.union b c)) in
  let inter = ExprSet.inter in
  match e with
    Equal (a, b) ->
    let l_tms = non_atoms_of_expr a in
    let r_tms = non_atoms_of_expr b in
    union (inter l_tms r_tms)
          (gather_gen_tms' a)
          (gather_gen_tms' b)
  | Cond (a, b, c)
       when ident (c, Abv "T") = Id_Equal ->
     (* This Cons is an implication *)
     let l_tms = non_atoms_of_expr a in
     let r_tms = non_atoms_of_expr b in
     union (inter l_tms r_tms)
           (gather_gen_tms' a)
           (gather_gen_tms' b)
  | Cond (a, b, c) ->
     union (gather_gen_tms' a)
           (gather_gen_tms' b)
           (gather_gen_tms' c)
  | Car a -> gather_gen_tms' a
  | Cdr a -> gather_gen_tms' a
  | FunCall (_, args) ->
     let args_gts = List.map gather_gen_tms' args in
     List.fold_left ExprSet.union ExprSet.empty args_gts
  | _ -> ExprSet.empty

let rec tm_depth e =
  match e with
    Car a -> 1 + (tm_depth a)
  | Cdr a -> 1 + (tm_depth a)
  | Equal (a,b) -> 1 + (max (tm_depth a) (tm_depth b))
  | Cond (a,b,c) -> 1 + (max (tm_depth a) (max (tm_depth b) (tm_depth c)))
  | Cons (a,b) -> 1 + (max (tm_depth a) (tm_depth b))
  | FunCall (f, args) ->
     1 + (List.fold_right max (List.map tm_depth args) 0)
  | _ -> 1

let get_max_tms es =
  let cmp x y =
    match tm_depth x > tm_depth y with
      true -> 1
    | false -> -1
  in
  let rec elim_sub_tms es =
    match es with
      [] -> []
    | (x::xs) -> if (List.exists (fun y -> occurs x y) xs) then
                   elim_sub_tms xs
                 else x :: (elim_sub_tms xs)
  in
  let es' = List.fast_sort cmp es in
  elim_sub_tms es'

let gather_gen_tms e =
  get_max_tms(ExprSet.elements (gather_gen_tms' e))

let mk_gen_const () =
  let n = !num_gen_consts in
  let c = Const (sprintf "GENRL%d" (n + 1)) in
  let _ = num_gen_consts := n+1 in
  c

let gen_once e gt =
  let ignore_te e =
    match expand_abvs e with
      Cons (Nil, Nil) -> true
    | FunCall(f, _)
         when (get_def f).fun_body = Cons (Nil, Nil) -> true
    | _ -> false in
  let gen_c = mk_gen_const () in
  fprintf std_formatter "@.Generalize common subterms by replacing %a by %a.@."
          pp_expr gt pp_expr gen_c ;
  let gt_type_expr = type_expr gt in
  let gt_type_hyp = subst gt_type_expr (Var "X") gen_c in
  let e' = subst e gt gen_c in
  if not(ignore_te gt_type_expr) then
    FunCall("IMPLIES", [gt_type_hyp; e'])
  else e'

let generalize e =
  let gts = List.rev (gather_gen_tms e)
  in if gts <> [] then
       let e_ref = ref e in
       let _ = List.iter (fun gt -> e_ref := gen_once (!e_ref) gt) gts in
       let _ = fprintf std_formatter "@.The generalized term is:@.@.%a@."
                       pp_expr (!e_ref) in
       !e_ref
     else
       e

(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
(*  Induction                                                                *)
(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)

exception GiveUp of string

(* TODO: Make sure all CAR_ARGs are unique in a prover run. *)

type ext_fault =
    { fault : fault ref;
      (* args = args appearing in the bomb_lst of the fault *)
      args  : expr list }

let ext_faults = ref []

let remove_dups lst =
  let seen = Hashtbl.create (List.length lst) in
  let not_seen_yet x =
    let s = not (Hashtbl.mem seen x) in
    Hashtbl.replace seen x ();
    s
  in
  List.filter not_seen_yet lst

(* Given a fault f, construct an extended fault for f.  This extended
   fault contains a pointer to f and an explicit args_list for f. *)

let extend_fault f =
  let rec arg_of_tm tm =
    match tm with
      Const c -> tm
    | Car a -> arg_of_tm a
    | Cdr a -> arg_of_tm a
    | a -> a in
  let args_of_pocket p =
    List.map arg_of_tm p in
  let bs = f.bomb_lst in
  { fault = ref f;
    args = remove_dups (List.flatten (List.map args_of_pocket bs)) }

let merge_faults f1 f2 =
  let b' = remove_dups (List.append f1.bomb_lst f2.bomb_lst) in
  let f' = ExprSet.union (expr_set f1.failures) (expr_set f2.failures) in
  { bomb_lst = b';
    failures = ExprSet.elements f' }

let merge_ext_faults' f1 f2 =
  let a1, a2 = expr_set f1.args, expr_set f2.args in
  let a' = ExprSet.inter a1 a2 in
  if a' <> ExprSet.empty then
    Some { fault = ref (merge_faults !(f1.fault) !(f2.fault));
           args = ExprSet.elements a' }
  else
    None

(* Need to finish merging for the general n>2 case! *)

let rec merge_ext_faults () =
  if List.length (!ext_faults) < 2 then ()
  else
    let f1, f2 = List.nth (!ext_faults) 0, List.nth (!ext_faults) 1 in
    match merge_ext_faults' f1 f2 with
      Some f -> (fprintf std_formatter "@.Merged two faults into one.@.";
                 ext_faults := f :: (List.tl (List.tl (!ext_faults)));
                 if (List.length (!ext_faults)) > 1
                 then fprintf std_formatter "@.Total number of faults: %d.@."
                              (List.length (!ext_faults));
                 merge_ext_faults ();
                 )
    | None -> ()

let pick_ind_vars faults =
  let base_ext_faults = List.map extend_fault faults in

  (* Keep only the faults whose arg_list contains only Skolem constants *)

  let good_ext_faults = List.filter
                          (fun ef ->
                           List.for_all (fun x -> match x with
                                                    Const _ -> true
                                                  | _ -> false)
                                        ef.args)
                          base_ext_faults in

  (* We also record them in the ext_faults global for later use *)

  let _ = ext_faults := good_ext_faults in
  let _ = merge_ext_faults () in

  (* We just return the first now. Will improve! *)

  List.hd (!ext_faults)

let rec conj_tms tms =
  match tms with
    [] -> Abv "T"
  | [tm] -> tm
  | (tm :: tms) -> FunCall("AND", [tm; conj_tms tms])

let induct e =
  let e = eval e in
  let _ = if List.length analysis.faults = 0 then
            raise (GiveUp "Nothing to induct upon in at least one conjunct") in
  let pp = fprintf std_formatter in
  let induct_ext_fault = pick_ind_vars analysis.faults in
  let induct_fault = !(induct_ext_fault.fault) in
  let induct_tms = induct_ext_fault.args in
  let base_cases = List.map (fun x -> subst e x Nil) induct_tms in
  (* let _ = List.map print_expr base_cases in *)
  let base_conj = conj_tms base_cases in
  let use_car_const arg = List.exists (List.mem (Car arg))
                                      induct_fault.bomb_lst in
  let use_cdr_const arg = List.exists (List.mem (Cdr arg))
                                      induct_fault.bomb_lst in
  let car_arg arg =
    match arg with
      Const s -> Const (s ^ "1")
    | _ -> raise (GiveUp "Cannot create CAR_ARG for non-constant term")
  in
  let ih_for_arg arg =
    match use_car_const arg, use_cdr_const arg with
      true, true -> let ih_1 = (subst e arg (car_arg arg)) in
                    let ih_2 = e in
                    conj_tms [ih_1; ih_2]
    | false, true -> e
    | true, false -> subst e arg (car_arg arg)
    | _ -> raise (GiveUp "Suitable IH cannot be formed") in
  let ic_for_arg arg = subst e arg (Cons (car_arg arg, arg)) in
  let s = String.concat " and " (List.map (fun (Const x) -> x) induct_tms) in
  let _ = pp "@.Induct on %s.@." s in
  FunCall("AND", [base_conj;
                  FunCall("IMPLIES", [conj_tms (List.map ih_for_arg induct_tms);
                                      conj_tms (List.map ic_for_arg induct_tms)])])

(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
(*  Main prover loop                                                         *)
(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)

let rec prove' e top limit =
  if limit <= 0 then raise (GiveUp "Prover effort limit exceeded");
  let pp = fprintf std_formatter in
  let proved x = ident (x, Abv "T") = Id_Equal in
  let e_nil x = ident (x, Nil) = Id_Equal in
  if top then pp "@.Theorem to be proved:@.@."
  else pp "@.The theorem to be proved is now:@.@.";
  print_expr e;
  let e = normalate e in
  if proved e then pp "@.@.Q.E.D.@.@."
  else if e_nil e then
    raise (GiveUp "Obviously, the proof attempt has failed")
  else
    let e' = fertilize e in
    if e <> e' then
        prove' e' false (limit-1)
    else
      begin
        match e' with
          Cond (p, q, Nil) ->
          let p' = generalize p in
          let _ = pp "@.Must try induction.@." in
          prove' (Cond (induct p', q, Nil)) false (limit-1)
        | _ ->
           let e'' = generalize e' in
           let _ = pp "@.Must try induction.@." in
           prove' (induct e'') false (limit-1)
      end

let prove ?(limit=10) e =
  let pp = fprintf std_formatter in
  num_fert_tms := 0;
  num_gen_consts := 0;
  try
    prove' e true limit
  with
    GiveUp s -> pp "@.--- We give up: %s. --- @.@." s

(* Our base function definitions *)

let base_defs = [

  { fun_name = "ZEROP";
    fun_args = ["X"];
    fun_body = Equal (Var "X", Abv "0");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "ADD1";
    fun_args = ["X"];
    fun_body = Cons (Nil, Var "X");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "SUB1";
    fun_args = ["X"];
    fun_body = Cdr (Var "X");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "LENGTH";
    fun_args = ["X"];
    fun_body = Cond (Var "X", FunCall("ADD1", [FunCall("LENGTH", [Cdr (Var "X")])]), Abv "0");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "ADD";
    fun_args = ["X"; "Y"];
    fun_body = Cond (FunCall ("ZEROP", [Var "X"]),
                     FunCall ("LENGTH", [Var "Y"]),
                     FunCall ("ADD1", [FunCall ("ADD", [FunCall ("SUB1", [Var "X"]);
                                                        Var "Y"])]));
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "LTE";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "X", Cond (Var "Y",
                                    FunCall ("LTE", [FunCall ("SUB1", [Var "X"]);
                                                     FunCall ("SUB1", [Var "Y"])]),
                                    Nil),
                     Abv "T");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "ADDTOLIST";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "Y",
                     Cond (FunCall ("LTE", [Var "X"; Car (Var "Y")]),
                           Cons (Var "X", Var "Y"),
                           Cons (Car (Var "Y"), (FunCall ("ADDTOLIST", [Var "X"; Cdr (Var "Y")])))),
                     Cons (Var "X", Nil));
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "AND";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "X", Cond(Var "Y", Abv "T", Nil), Nil);
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "APPEND";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "X",
                     Cons (Car (Var "X"), FunCall ("APPEND", [Cdr (Var "X"); Var "Y"])),
                     Var "Y");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "ASSOC";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "Y",
                     Cond (Car (Var "Y"),
                           Cond (Equal (Var "X", Car (Car (Var "Y"))),
                                 Car (Var "Y"),
                                 FunCall ("ASSOC", [Var "X"; Cdr (Var "Y")])),
                           FunCall ("ASSOC", [Var "X"; Cdr (Var "Y")])),
                     Nil);
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "BOOLEAN";
    fun_args = ["X"];
    fun_body = Cond (Var "X", Equal (Var "X", Abv "T"), Abv "T");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "CDRN";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "Y", Cond (Var "X",
                                    FunCall ("CDRN", [FunCall ("SUB1", [Var "X"]);
                                                      Cdr (Var "Y")]),
                                    Var "Y"),
                     Nil);
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "CONSNODE";
    fun_args = ["X"; "Y"];
    fun_body = Cons (Nil, Cons (Var "X", Var "Y"));
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "COUNT";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "Y",
                     Cond (Equal (Var "X", Car (Var "Y")),
                           FunCall("ADD1", [FunCall("COUNT", [Var "X"; Cdr (Var "Y")])]),
                           FunCall("COUNT", [Var "X"; Cdr (Var "Y")])),
                     Abv "0");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "CONSTTRU";
    fun_args = ["X"];
    fun_body = Abv "T";
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "COPY";
    fun_args = ["X"];
    fun_body = Cond (Var "X",
                     Cons (FunCall ("COPY", [Car (Var "X")]), FunCall("COPY", [Cdr (Var "X")])),
                     Nil);
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "DOUBLE";
    fun_args = ["X"];
    fun_body = Cond (FunCall("ZEROP", [Var "X"]),
                     Abv "0",
                     FunCall("ADD", [Abv "2"; FunCall("DOUBLE", [FunCall("SUB1", [Var "X"])])]));
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "ELEMENT";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "Y",
                     Cond (FunCall("ZEROP", [Var "X"]),
                           Car (Var "Y"),
                           FunCall("ELEMENT", [FunCall("SUB1", [Var "X"]);
                                               Cdr (Var "Y")])),
                     Nil);
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "EQUALP";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "X",
                     Cond (Var "Y",
                           Cond (FunCall("EQUALP", [Car (Var "X"); Car (Var "Y")]),
                                 FunCall("EQUALP", [Cdr (Var "X"); Cdr (Var "Y")]),
                                 Nil),
                           Nil),
                     Cond (Var "Y", Nil, Abv "T"));
    fun_props = ref [];
    fun_type = ref None };

 (*
  { fun_name = "ODD";
    ... }

  { fun_name = "EVEN1";
    fun_args = ["X"];
    fun_body = Cond (FunCall("ZEROP", [Var "X"]),
                     Abv "T",
                     FunCall("ODD", [FunCall("SUB1", [Var "X"])]));
    fun_props = ref [];
    fun_type = ref None };
  *)

  { fun_name = "GT";
    fun_args = ["X"; "Y"];
    fun_body = Cond(Var "X", Cond(Var "Y",
                                  FunCall("GT", [FunCall("SUB1", [Var "X"]); FunCall("SUB1", [Var "Y"])]),
                                  Abv "T"),
                    Nil);
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "HALF";
    fun_args = ["X"];
    fun_body = Cond (FunCall("ZEROP", [Var "X"]),
                     Abv "0",
                     Cond (FunCall("ZEROP", [FunCall("SUB1", [Var "X"])]),
                           Abv "0",
                           FunCall("ADD1", [FunCall("HALF", [FunCall("SUB1", [FunCall("SUB1", [Var "X"])])])])));
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "IMPLIES";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "X", Cond (Var "Y", Abv "T", Nil), Abv "T");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "MEMBER";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "Y",
                     Cond (Equal (Var "X", Car (Var "Y")),
                           Abv "T",
                           FunCall ("MEMBER", [Var "X"; Cdr (Var "Y")])),
                     Nil);
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "MULT";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "X",
                     Cond (Var "Y",
                           FunCall("ADD", [Var "Y";
                                           FunCall("MULT",
                                                   [FunCall("SUB1", [Var "X"]);
                                                    Var "Y"])]),
                           Abv "0"),
                     Abv "0");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "INTERSECT";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "X",
                     Cond (FunCall ("MEMBER", [Car (Var "X"); Var "Y"]),
                           Cons (Car (Var "X"), FunCall("INTERSECT", [Cdr (Var "X"); Var "Y"])),
                           FunCall("INTERSECT", [Cdr (Var "X"); Var "Y"])),
                     Nil);
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "NOT";
    fun_args = ["X"];
    fun_body = Cond (Var "X", Nil, Abv "T");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "NUMBERP";
    fun_args = ["X"];
    fun_body = Cond(Var "X", Cond (Car (Var "X"),
                                   Nil,
                                   FunCall("NUMBERP", [Cdr (Var "X")])),
                    Abv "T");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "OR";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "X", Abv "T", Cond (Var "Y", Abv "T", Nil));
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "ORDERED";
    fun_args = ["X"];
    fun_body = Cond (Var "X",
                     Cond (Cdr (Var "X"),
                           Cond (FunCall("LTE", [Car (Var "X");
                                                 Car (Cdr (Var "X"))]),
                                 FunCall("ORDERED", [Cdr (Var "X")]),
                                 Nil),
                           Abv "T"),
                     Abv "T");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "PAIRLIST";
    fun_args = ["X"; "Y"];
    fun_body = Cond (Var "X", Cond (Var "Y",
                                    Cons (Cons (Car (Var "X"), Car (Var "Y")),
                                          FunCall("PAIRLIST", [Cdr (Var "X");
                                                               Cdr (Var "Y")])),
                                    Cons (Cons (Car (Var "X"), Nil),
                                          FunCall("PAIRLIST", [Cdr (Var "X"); Nil]))),
                     Nil);
    fun_props = ref [];
    fun_type = ref None };


  { fun_name = "REVERSE";
    fun_args = ["X"];
    fun_body = Cond (Var "X", FunCall("APPEND", [FunCall("REVERSE", [Cdr (Var "X")]);
                                                 Cons(Car (Var "X"), Nil)]),
                     Nil);
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "SORT";
    fun_args = ["X"];
    fun_body = Cond (Var "X",
                     FunCall("ADDTOLIST", [Car (Var "X");
                                           FunCall("SORT", [Cdr (Var "X")])]),
                     Nil);
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "SUBSET";
    fun_args = ["X"; "Y"];
    fun_body = Cond(Var "X", Cond(FunCall("MEMBER", [Car (Var "X"); Var "Y"]),
                                  FunCall("SUBSET", [Cdr (Var "X"); Var "Y"]),
                                  Nil),
                    Abv "T");
    fun_props = ref [];
    fun_type = ref None };

  { fun_name = "UNION";
    fun_args = ["X"; "Y"];
    fun_body = Cond(Var "X",
                    Cond(FunCall("MEMBER", [Car (Var "X"); Var "Y"]),
                         FunCall("UNION", [Cdr (Var "X"); Var "Y"]),
                         Cons (Car (Var "X"), FunCall("UNION", [Cdr (Var "X"); Var "Y"]))),
                    Var "Y");
    fun_props = ref [];
    fun_type = ref None };

 ]

let init () =
  fprintf std_formatter "%s@.System initialization:@.%s@." div div;
  List.iter define base_defs;
  fprintf std_formatter "%s@.Let the games begin.@.%s@." div div

let _ = init ()

(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
(*  Examples                                                                 *)
(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)

(* Helper functions for constructing ASTs in examples *)

let f_implies (x,y) = FunCall("IMPLIES", [x;y]);;
let f_or (x,y) = FunCall("OR", [x;y]);;
let f_and (x,y) = FunCall("AND", [x;y]);;
let f_not x = FunCall("NOT", [x]);;
let f_member (x,y) = FunCall("MEMBER", [x;y]);;
let f_assoc (x,y) = FunCall("ASSOC", [x;y]);;
let f_append (x,y) = FunCall("APPEND", [x;y]);;
let f_intersect (x,y) = FunCall("INTERSECT", [x;y]);;
let f_union (x,y) = FunCall("UNION", [x;y]);;
let f_length x = FunCall("LENGTH", [x]);;
let f_reverse x = FunCall("REVERSE", [x]);;
let f_subset (x,y) = FunCall("SUBSET", [x;y]);;
let f_copy x = FunCall("COPY", [x]);;
let f_pairlist (x,y) = FunCall("PAIRLIST", [x;y]);;
let f_add (x,y) = FunCall("ADD", [x;y]);;
let f_lte (x,y) = FunCall("LTE", [x;y]);;
let f_gt (x,y) = FunCall("GT", [x;y]);;
let f_numberp x = FunCall("NUMBERP", [x]);;
let f_ordered x = FunCall("ORDERED", [x]);;
let f_sort x = FunCall("SORT", [x]);;
let f_addtolist (x,y) = FunCall("ADDTOLIST", [x;y]);;
let f_cdrn (x,y) = FunCall("CDRN", [x;y]);;
let f_count (x,y) = FunCall("COUNT", [x;y]);;
let f_double x = FunCall("DOUBLE", [x]);;
let f_half x = FunCall("HALF", [x]);;
let f_element (x,y) = FunCall("ELEMENT", [x;y]);;
let f_pairlist (x,y) = FunCall("PAIRLIST", [x;y]);;
let f_equalp (x,y) = FunCall("EQUALP", [x;y]);;
let f_mult (x,y) = FunCall("MULT", [x;y]);;

let c_a, c_b, c_c, c_d = Const "A", Const "B", Const "C", Const "D";;


(* -----> E X A M P L E   P R O O F S -----> *)


(* Can prove with just induct and normalate *)

let _ = prove(Equal(f_copy(c_a), c_a));;

let _ = prove(Equal(f_append(c_a, f_append(c_b, c_c)),
                    f_append(f_append(c_a, c_b), c_c)));;

let _ = prove(f_implies(f_member(c_a, c_b),
                        f_member(c_a, f_append(c_b, c_c))));;

let _ = prove(f_implies(f_member(c_a, c_b),
                        f_member(c_a, f_append(c_c, c_b))));;

let _ = prove(f_implies(f_or(f_member(c_a, c_b), f_member(c_a, c_c)),
                        f_member(c_a, f_append(c_b, c_c))));;

let _ = prove(f_implies(f_subset(c_a, c_b),
                        Equal(f_union(c_a, c_b), c_b)));;

let _ = prove(f_implies(f_subset(c_a, c_b),
                        Equal(f_intersect(c_a, c_b), c_a)));;

let _ = prove(Equal(f_length(c_a), f_length(f_copy(c_a))));;

let _ = prove(Equal(f_length(c_a), f_length(f_pairlist(c_a, c_a))));;

let _ = prove(f_implies(f_numberp(c_a), Equal(f_add(c_a, Abv "0"), c_a)));;

let _ = prove(f_numberp(f_length(c_a)));;

let _ = prove(f_numberp(f_add(c_a, c_b)));;

let _ = prove(f_gt(f_length(Cons(c_a, c_b)), f_length c_b));;

let _ = prove(f_implies(f_numberp(c_a),
                        Equal(c_a, f_mult(Abv "1", c_a))));;

let _ = prove(Equal(f_mult(Abv "0", c_a), Abv "0"));;

let _ = prove(Equal(f_mult(c_a, Abv "0"), Abv "0"));;

let _ = prove(f_implies(Equal(f_append(c_a, c_b),
                              f_append(c_a, c_c)),
                        Equal(c_b, c_c)));;


(* Can prove with just induct, normalate and fertilize *)

let _ = prove(Equal(Equal(c_a, c_b), Equal(c_b, c_a)));;

let _ = prove(f_implies(f_and(Equal(c_a, c_b), Equal(c_b, c_c)),
                        Equal(c_a, c_c)));;

let _ = prove(f_implies(f_and(f_member(c_a, c_b), f_member(c_a, c_c)),
                        f_member(c_a, f_intersect(c_b, c_c))));;

let _ = prove(f_implies(f_or(f_member(c_a, c_b), f_member(c_a, c_c)),
                        f_member(c_a, f_union(c_b, c_c))));;

let _ = prove(f_implies(f_ordered(c_a), Equal(c_a, f_sort(c_a))));;





(* Before generalization, we could prove this with just induct, normalate and fertilize.
   When we generalized without typeexpr support, they failed. But now that we have
   typeexpr's, they succeed! *)

let _ = prove(Equal(f_add(c_a, f_add(c_b, c_c)),
                    f_add(f_add(c_a, c_b), c_c)));;

let _ = prove(Equal(f_length(f_append(c_a, c_b)),
                    f_add(f_length(c_a), f_length(c_b))));;



(* Can prove with normalate / induct / fertilize / generalize without typeexpr's *)
(* Can also prove now that we have support for typeexpr's! *)

let _ = prove(f_numberp(f_add(c_a, c_a)));;

let _ = prove(Equal(f_length(f_reverse(c_d)), f_length(c_d)));;

let _ = prove(Equal(f_reverse(f_reverse(c_a)), c_a));;

let _ = prove(Equal(f_member(c_a, f_sort c_b), f_member(c_a, c_b)));;


(* Can prove with all of the above + simple merging of two faults *)

let _ = prove(f_implies(f_and(f_not(Equal(c_a, Car c_b)),
                              f_member(c_a, c_b)),
                        f_member(c_a, Cdr c_b)));;

let _ = prove(f_implies(f_ordered(f_append(c_a, c_b)), f_ordered(c_a)));;

let _ = prove(Equal(f_reverse(f_append(c_a, c_b)),
                    f_append(f_reverse(c_b), f_reverse(c_a))));;


(* Couldn't prove before new addition to fertilize, 17. But now we can! *)

let _ = prove(Equal(f_length(f_append(c_a, c_b)), f_length(f_append(c_b, c_a))));;

let _ = prove(Equal(f_add(c_a, c_b), f_add(c_b, c_a)));;

let _ = prove(Equal(f_add(c_a, f_add(c_b, c_c)), f_add(f_add(c_a, c_b), c_c)));;

let _ = prove(Equal(f_length(c_a), f_length(f_sort(c_a))));;

let _ = prove(Equal(f_count(c_a, c_b), f_count(c_a, f_sort(c_b))));;



(* Can't prove:

let _ = prove(Equal(f_member(c_a, c_b),
                    f_not(Equal(f_assoc(c_a, f_pairlist(c_b, c_c)), Nil))));;


let _ = prove(f_or(f_lte(c_a, c_b), f_lte(c_b, c_a)));;

let _ = prove(f_implies(f_and(f_gt(c_a, c_b), f_gt(c_b, c_c)),
                        f_gt(c_a, c_c)));;

let _ = prove(f_implies(f_gt(c_a, c_b), f_not(f_gt(c_b, c_a))));;

let _ = prove(f_lte(c_a, f_append(c_b, c_a)));;

let _ = prove(f_or(f_lte(c_a, c_b), f_lte(c_b, c_a)));;

let _ = prove(f_lte(f_cdrn(c_a, c_b), c_b));;

let _ = prove(Equal(Equal(f_sort(c_a), c_a), f_ordered(c_a)));;

let _ = prove(f_lte(f_half(c_a), c_a));;

let _ = prove(f_lte(c_a, f_double(c_a)));;

let _ = prove(f_implies(f_numberp(c_a), Equal(f_half(f_double(c_a)), c_a)));;

let _ = prove(Equal(f_element(c_b, c_a),
                    f_element(f_append(c_c, c_b), f_append(c_c, c_a))));;


*** Needs simulantenous induction on multiple variables:

let _ = prove(f_implies(f_ordered(f_append(c_a, c_b)), f_ordered(c_b)));;

(* Performs an interesting bad generalization *)

let _ = prove(f_implies(f_element(c_b, c_a),
                        f_member(f_element(c_b, c_a), c_a)));;

let _ = prove(Equal(f_equalp(c_a, c_b), Equal(c_a, c_b)));;

let _ = prove(f_implies(f_and(f_equalp(c_a, c_b), f_equalp(c_b, c_c)),
                        f_equalp(c_a, c_c)));;

let _ = prove(Equal(f_mult(c_a, f_mult(c_b, c_c)),
                    f_mult(f_mult(c_a, c_b), c_c)));;

let _ = prove(f_implies(f_numberp(c_a),
                        Equal(c_a, f_mult(c_a, Abv "1"))));;

 *)

(* Experiments with basic expressions and definitions *)

(*

let ex1 = Cond (Equal(Nil, Nil), Cons(Nil, Nil), Nil)
    in print_expr ex1;;

let ex2 = Cond (Equal(Nil, Const "A"), Cons(Nil, Nil), Nil)
    in print_expr ex2;;

let def_append = { fun_name = "APPEND";
                   fun_args = ["X"; "Y"];
                   fun_body = Cond(Var "X",
                                   Cons(Car (Var "X"),
                                        FunCall ("APPEND", [Cdr (Var "X"); (Var "Y")])),
                                   Var "Y");
                   fun_props = ref [] };;

let def_add1 = { fun_name = "ADD1";
                 fun_args = ["X"];
                 fun_body = Cons(Nil, Var "X");
                 fun_props = ref [] };;

print_def def_append;;
print_def def_add1;;

define def_append;;
show_def "APPEND";;

let f2 = Equal(FunCall("ADD", [Abv "3"; Abv "5"]),
               Abv "8")
    in expand_abvs f2;;

(* Ident examples from p110 *)

let e1, e2 = Cons (Const "A", Const "B"), Cons (Const "A", Const "B") in
    ident (e1, e2);;

let e1, e2 = Cons (Abv "0", Nil), Abv "1" in
    ident (e1, e2);;

let e1, e2 = Cons (Const "A", Const "B"), Nil in
    ident (e1, e2);;

let e1, e2 = Cons (Const "A", Const "B"), Const "A" in
    ident (e1, e2);;

let e1, e2 = Cons (Const "A", Const "B"), Const "B" in
    ident (e1, e2);;

let e1, e2 = Cons (Const "A", Const "B"), Const "C" in
    ident (e1, e2);;

let e1, e2 = Cons (Const "A", Const "B"), Cons (Const "A", Const "C") in
    ident (e1, e2);;

(* Explicit sublists *)

explicit_sublist (Nil, Nil);;
explicit_sublist (Cons (Nil, Nil), Nil);;
explicit_sublist (Nil, Cons (Nil, Nil));;
explicit_sublist (Const "A", Const "B");;
explicit_sublist (Const "A", Cons (Const "A", Nil));;

(* Eval examples from p111 *)

let e = eval (Cons (Const "A", Const "B")) in
    print_expr e;;

let e = eval (Car (Cons (Const "A", Const "B"))) in
    print_expr e;;

let e = eval (Cons (Car (Cons (Const "A", Const "B")), Nil)) in
    print_expr e;;

let e = eval (Equal (Abv "3", Cons (Nil, Abv "2"))) in
    print_expr e;;

let e = eval (Cond (Equal (Cdr (Cons (Const "A", Const "B")), Const "B"),
                    Car (Cons (Const "A", Const "B")),
                    Nil)) in
    print_expr e;;

let e = eval (Equal (Cons (Const "A", Const "B"),
                     Cons (Const "C", Const "B"))) in
    print_expr e;;

let e = eval (Cond (Const "A",
                    Cdr (Cons (Const "A", Const "B")),
                    Const "C")) in
    print_expr e;;

let e = eval (Equal (Cons (Cond (Const "A",
                                 Cdr (Cons (Const "A", Const "B")),
                                 Const "C"),
                           Const "A"),
                     Const "A")) in
    print_expr e;;

(* Let's prove that 3 = 1 + 2 by evaluation! *)

let e = eval (Equal (Abv "3", Cons (Nil, Abv "2"))) in
    print_expr e;;

(* Let's prove that (APPEND NIL B) = B by evaluation! *)

let e =  eval (Equal (FunCall("APPEND", [Nil; Const "B"]), Const "B")) in
    print_expr e;;

(* Let's evaluate (REVERSE '(0 1)) *)

let e = eval (FunCall("REVERSE", [Cons(Nil,Cons(Cons(Nil,Nil),Nil))])) in
    print_expr e;;

(* Pretty-print all definitions *)

let _ = set_margin 75;;

let _ = show_defs ();;

(* More evaluation *)

let e = eval (FunCall ("APPEND", [Nil; Nil])) in
    print_expr e;;

let e = eval (FunCall ("APPEND", [Cons(Abv "1", Nil); Cons (Abv "2", Nil)])) in
    print_expr e;;

let e = eval (Cond (FunCall ("APPEND", [Nil; Nil]), Const "A", Const "B")) in
    print_expr e;;

let e = eval (Cond (Const "A", Const "B", FunCall ("APPEND", [Nil; Nil]))) in
    print_expr e;;

(* Eval examples with FunCall short-circuiting from p 115 *)


let e = eval (FunCall ("APPEND", [Cons (Const "A1", Const "A"); Const "B"])) in
    print_expr e;;

let e = eval (FunCall ("REVERSE", [Cons (Const "A1", Const "A")])) in
    print_expr e;;

let e = eval (FunCall ("MEMBER", [Const "A"; Cons (Const "B1", Const "B")])) in
    fprintf std_formatter "@.";
    print_expr e;;

let e = eval (FunCall ("COPY", [Const "A"])) in
    print_expr e;;

let e = eval (FunCall ("COPY", [Cons (Const "A1", Const "A")])) in
    fprintf std_formatter "@.";
    print_expr e;;

let e = eval (FunCall ("OR", [Cons (FunCall("REVERSE", [Const "A"]), Nil); Nil])) in
    print_expr e;;

(* Fault analysis examples *)

let e = eval (FunCall ("SUB1", [Const "A"])) in
    print_expr e;;

let e = eval (FunCall ("LTE", [Const "A"; Const "B"])) in
    print_expr e;;

let e = eval (FunCall ("LTE", [Const "A"; FunCall("ADD1", [Const "A"])])) in
    print_expr e;;

let e = eval (FunCall ("LTE", [FunCall("ADD1", [Const "A"]); Const "A"])) in
    print_expr e;;

let e = eval (FunCall ("OR", [FunCall ("LTE", [Const "A"; Const "B"]);
                              FunCall ("LTE", [Const "B"; Const "A"])])) in
    print_expr e;;

(* boolean *)

let _ = boolean (FunCall("MEMBER", [Const "A"; Const "B"]));;

let _ = boolean (FunCall("OR", [Const "A"; Const "B"]));;

let _ = boolean (FunCall("COPY", [Const "A"]));;

  (* normalization *)


  (* More eval examples - p133 *)

let _ = set_margin 70;;

let _ = for i = 1 to 10 do printf "\n" done;;

let e = FunCall("AND", [Equal(FunCall("APPEND", [Nil; FunCall("APPEND", [Const "B"; Const "C"])]),
                              FunCall("APPEND", [FunCall("APPEND", [Nil; Const "B"]); Const "C"]));
                        FunCall("IMPLIES", [Equal(FunCall("APPEND", [Const "A"; FunCall("APPEND", [Const "B"; Const "C"])]),
                                                  FunCall("APPEND", [FunCall("APPEND", [Const "A"; Const "B"]); Const "C"]));
                                            Equal(FunCall("APPEND", [Cons(Const "A1", Const "A"); FunCall("APPEND", [Const "B"; Const "C"])]),
                                                  FunCall("APPEND", [FunCall("APPEND", [Cons(Const "A1", Const "A"); Const "B"]); Const "C"]))])])
    in fprintf std_formatter "@.-----@.Associativity of APPEND:@.@.";
       print_expr e;
       ignore(normalate e);
       fprintf std_formatter "@.@."
;;

  (* Normalization example - p128/129 *)

let _ = for i = 1 to 10 do printf "\n" done;;

let e = Cond(Cond(Cond(Const "A", Const "B", Const "A"), Cond(Const "B", Abv "T", Nil), Abv "T"),
             Cond(Equal(Const "A", Cond(FunCall("GT", [Const "B"; Const "B"]), Const "A", Cons(Const "A1", Const "A"))),
                  Nil, Abv "T"),
             Cond(Const "A1", Nil, Nil))
    in fprintf std_formatter "@.-----@.Normalization example (p128/129):@.@.";
       print_expr e;
       ignore(normalate e);
       fprintf std_formatter "@.@."

;;

(* Normalation example - p134 *)

let _ = for i = 1 to 10 do printf "\n" done;;

let e = FunCall("IMPLIES", [FunCall("AND", [FunCall("GT", [Const "A"; Const "B"]);
                                            FunCall("GT", [Const "B"; Const "C"])]);
                            FunCall("GT", [Const "A"; Const "C"])])
    in fprintf std_formatter "@.-----@.Normalation example (p134):@.@.";
       print_expr e;
       ignore(normalate e);
       fprintf std_formatter "@.@."
;;

(* Normalation example *)

let _ = for i = 1 to 10 do printf "\n" done;;

let e = FunCall("IMPLIES", [FunCall("OR", [Equal(FunCall("SUB1", [FunCall("ADD1", [Const "A"])]), Const "A");
                                           Nil]);
                            Abv "T"])
    in fprintf std_formatter "@.-----@.Normalation example:@.@.";
       print_expr e;
       ignore(normalate e);
       fprintf std_formatter "@.@."
;;

(* Normalation example *)

let _ = for i = 1 to 10 do printf "\n" done;;

let e = Equal(FunCall("COPY", [Const "A"]), Const "A")
    in fprintf std_formatter "@.-----@.Normalation example (p163):@.@.";
       print_expr e;
       ignore(normalate e);
       fprintf std_formatter "@.@."
;;

let _ = for i = 1 to 10 do printf "\n" done;;

let e = FunCall("AND", [Equal(FunCall("COPY", [Nil]), Nil);
                        FunCall("IMPLIES",
                                [FunCall("AND", [Equal(FunCall("COPY", [Const "A1"]),
                                                       Const "A1");
                                                 Equal(FunCall("COPY", [Const "A"]),
                                                       Const "A")]);
                                 Equal(FunCall("COPY", [Cons(Const "A1", Const "A")]),
                                       Cons(Const "A1", Const "A"))])])
    in fprintf std_formatter "@.-----@.Normalation example (p163 - (EQUAL (COPY A) A) induction):@.@.";
       print_expr e;
       ignore(normalate e);
       fprintf std_formatter "@.@."

;;


(* Some eval/analysis experiments *)

let def_f =
 { fun_name = "F";
   fun_args = ["X"];
   fun_body = Cond(Var "X", Cons(Cdr(Cdr(Var "X")), FunCall("F", [Cdr (Var "X")])), Nil);
   fun_props = ref [] };;

define def_f;;

eval (FunCall("F", [Cons(Const "A", Cons(Const "B", Const "C"))]));;

(* Here we currently produce slightly different fault descriptions than
   given in Moore's thesis (p121): *)

let e = f_ordered(f_sort c_a) in
  eval e;;

 *)
