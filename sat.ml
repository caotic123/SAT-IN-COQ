let __ = let rec f _ = Obj.repr f in Obj.repr f
type __ = Obj.t

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type 'a option =
| Some of 'a
| None
[@@deriving show]

(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,_ -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| _,y -> y

(** val length : 'a1 list -> int **)

let rec length x = List.length x

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a



(** val add : int -> int -> int **)

let rec add n m = n + m

(** val max : int -> int -> int **)

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module Nat =
 struct
  (** val eq_dec : int -> int -> bool **)

  let rec eq_dec n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n1 -> eq_dec n0 n1)
        m)
      n
 end

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y::l0 -> let s = h y a in if s then true else in_dec h a l0

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t1 -> (f a)::(map f t1)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b::t1 -> f b (fold_right f a0 t1)

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x::tl -> if f x then Some x else find f tl

(** val nodup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec nodup decA = function
| [] -> []
| x::xs -> if in_dec decA x xs then nodup decA xs else x::(nodup decA xs)

(** val internal_eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let internal_eq_rew_r_dep _ _ hC =
  hC

type t0 =
| F1 of int
| FS of int * t0

(** val is_left : bool -> bool **)

let is_left = function
| true -> true
| false -> false

(** val solution_left : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let solution_left _ x _ =
  x

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)

  (** val eq_dec : positive -> positive -> bool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> false)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> false)
    | XH -> (match x0 with
             | XH -> true
             | _ -> false)
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val eq_dec : z -> z -> bool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos p0 -> Pos.eq_dec p p0
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg p0 -> Pos.eq_dec p p0
                 | _ -> false)
 end

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> true
    | _ -> false

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module KeyOrderedType =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module Raw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t*'elt) list

  (** val empty : 'a1 t **)

  let empty =
    []

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | [] -> true
  | _::_ -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | [] -> false
  | p::l ->
    let k',_ = p in
    (match X.compare k k' with
     | LT -> false
     | EQ -> true
     | GT -> mem k l)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | [] -> None
  | p::s' ->
    let k',x = p in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find k s')

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | [] -> (k,x)::[]
  | p::l ->
    let k',y = p in
    (match X.compare k k' with
     | LT -> (k,x)::s
     | EQ -> (k,x)::l
     | GT -> (k',y)::(add k x l))

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | [] -> []
  | p::l ->
    let k',x = p in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> (k',x)::(remove k l))

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | [] -> acc
    | p::m' -> let k,e = p in fold f m' (f k e acc)

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | [] -> (match m' with
             | [] -> true
             | _::_ -> false)
    | p::l ->
      let x,e = p in
      (match m' with
       | [] -> false
       | p0::l' ->
         let x',e' = p0 in
         (match X.compare x x' with
          | EQ -> if cmp e e' then equal cmp l l' else false
          | _ -> false))

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | [] -> []
  | p::m' -> let k,e = p in (k,(f e))::(map f m')

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | [] -> []
  | p::m' -> let k,e = p in (k,(f k e))::(mapi f m')

  (** val option_cons :
      key -> 'a1 option -> (key*'a1) list -> (key*'a1) list **)

  let option_cons k o l =
    match o with
    | Some e -> (k,e)::l
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | [] -> []
  | p::l -> let k,e = p in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | [] -> []
  | p::l' -> let k,e' = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | [] -> map2_r f
  | p::l ->
    let k,e = p in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f m
    | p0::l' ->
      let k',e' = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option*'a2 option) t **)

  let rec combine m = match m with
  | [] -> map (fun e' -> None,(Some e'))
  | p::l ->
    let k,e = p in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e0 -> (Some e0),None) m
    | p0::l' ->
      let k',e' = p0 in
      (match X.compare k k' with
       | LT -> (k,((Some e),None))::(combine l m')
       | EQ -> (k,((Some e),(Some e')))::(combine l l')
       | GT -> (k',(None,(Some e')))::(combine_aux l'))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1*'a2) list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key*'a3)
      list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 []

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option*'a2 option) option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o,o')
    | None -> (match o' with
               | Some _ -> Some (o,o')
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module type Int =
 sig
  type t

  val i2z : t -> z

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int =
 struct
  type t = z

  (** val _0 : z **)

  let _0 =
    Z0

  (** val _1 : z **)

  let _1 =
    Zpos XH

  (** val _2 : z **)

  let _2 =
    Zpos (XO XH)

  (** val _3 : z **)

  let _3 =
    Zpos (XI XH)

  (** val add : z -> z -> z **)

  let add =
    Z.add

  (** val opp : z -> z **)

  let opp =
    Z.opp

  (** val sub : z -> z -> z **)

  let sub =
    Z.sub

  (** val mul : z -> z -> z **)

  let mul =
    Z.mul

  (** val max : z -> z -> z **)

  let max =
    Z.max

  (** val eqb : z -> z -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : z -> z -> bool **)

  let ltb =
    Z.ltb

  (** val leb : z -> z -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : z -> z -> bool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : z -> z -> bool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then true else false

  (** val ge_lt_dec : z -> z -> bool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then false else true

  (** val i2z : t -> z **)

  let i2z n =
    n
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t2, k, y, t3, t4) ->
    f0 t2 (tree_rect f f0 t2) k y t3 (tree_rect f f0 t3) t4

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t2, k, y, t3, t4) ->
    f0 t2 (tree_rec f f0 t2) k y t3 (tree_rec f f0 t3) t4

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> int **)

  let rec cardinal = function
  | Leaf -> 0
  | Node (l, _, _, r, _) -> (add (cardinal l) (cardinal r)) + 1

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _, _) -> false

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (l, y, _, r, _) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ -> true
     | GT -> mem x r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x = function
  | Leaf -> None
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ -> Some d
     | GT -> find x r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x e r =
    Node (l, x, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x d r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.add hr I._2)
    then (match l with
          | Leaf -> assert_false l x d r
          | Node (ll, lx, ld, lr, _) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx ld (create lr x d r)
            else (match lr with
                  | Leaf -> assert_false l x d r
                  | Node (lrl, lrx, lrd, lrr, _) ->
                    create (create ll lx ld lrl) lrx lrd (create lrr x d r)))
    else if I.gt_le_dec hr (I.add hl I._2)
         then (match r with
               | Leaf -> assert_false l x d r
               | Node (rl, rx, rd, rr, _) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x d rl) rx rd rr
                 else (match rl with
                       | Leaf -> assert_false l x d r
                       | Node (rll, rlx, rld, rlr, _) ->
                         create (create l x d rll) rlx rld
                           (create rlr rx rd rr)))
         else create l x d r

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x d = function
  | Leaf -> Node (Leaf, x, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d l) y d' r
     | EQ -> Node (l, y, d, r, h)
     | GT -> bal l y d' (add x d r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree*(key*'a1) **)

  let rec remove_min l x d r =
    match l with
    | Leaf -> r,(x,d)
    | Node (ll, lx, ld, lr, _) ->
      let l',m = remove_min ll lx ld lr in (bal l' x d r),m

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let s2',p = remove_min l2 x2 d2 r2 in let x,d = p in bal s1 x d s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d r
     | EQ -> merge l r
     | GT -> bal l y d (remove x r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d ->
      let rec join_aux r = match r with
      | Leaf -> add x d l
      | Node (rl, rx, rd, rr, rh) ->
        if I.gt_le_dec lh (I.add rh I._2)
        then bal ll lx ld (join lr x d r)
        else if I.gt_le_dec rh (I.add lh I._2)
             then bal (join_aux rl) rx rd rr
             else create l x d r
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t1 =
    t1.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t1 =
    t1.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t1 =
    t1.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let m2',xd = remove_min l2 x2 d2 r2 in join m1 (fst xd) (snd xd) m2')

  (** val elements_aux : (key*'a1) list -> 'a1 tree -> (key*'a1) list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d, r, _) -> elements_aux ((x,d)::(elements_aux acc r)) l

  (** val elements : 'a1 tree -> (key*'a1) list **)

  let elements m =
    elements_aux [] m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d, r, _) -> fold f r (f x d (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e0, t1, e1) -> f0 k e0 t1 e1 (enumeration_rect f f0 e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e0, t1, e1) -> f0 k e0 t1 e1 (enumeration_rec f f0 e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x, d, r, _) -> cons l (More (x, d, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d1 cont = function
  | End -> false
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> if cmp d1 d2 then cont (cons r2 e3) else false
     | _ -> false)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> true
  | More (_, _, _, _) -> false

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((map f l), x, (f d), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((mapi f l), x, (f x d), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, _) ->
    (match f x d with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d o -> f (Some d) o)
      (map_option (fun _ d -> f (Some d) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem

    (** val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rect x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rec x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    (** val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rect x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rec x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

    (** val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (l, x, d, r) -> f l x d r __ __ __
    | R_bal_1 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f0 l x d r __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_2 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f1 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_3 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f2 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_4 (l, x, d, r) -> f3 l x d r __ __ __ __ __
    | R_bal_5 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f4 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_6 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f5 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_7 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f6 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_8 (l, x, d, r) -> f7 l x d r __ __ __ __

    (** val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rec f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (l, x, d, r) -> f l x d r __ __ __
    | R_bal_1 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f0 l x d r __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_2 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f1 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_3 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f2 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_4 (l, x, d, r) -> f3 l x d r __ __ __ __ __
    | R_bal_5 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f4 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_6 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f5 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_7 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f6 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_8 (l, x, d, r) -> f7 l x d r __ __ __ __

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    (** val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rect x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 r0 _res r1)

    (** val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rec x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree*(key*'elt))
       * 'elt coq_R_remove_min * 'elt tree * (key*'elt)

    (** val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree ->
        (key*'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
        tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rect f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r) -> f l x d r __
    | R_remove_min_1 (l, x, d, r, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rect f f0 ll lx ld lr _res r1) l' m __

    (** val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree ->
        (key*'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
        tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rec f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r) -> f l x d r __
    | R_remove_min_1 (l, x, d, r, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rec f f0 ll lx ld lr _res r1) l' m __

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key*'elt) * key * 'elt

    (** val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key*'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rect f f0 f1 _ _ _ = function
    | R_merge_0 (s1, s2) -> f s1 s2 __
    | R_merge_1 (s1, s2, _x, _x0, _x1, _x2, _x3) ->
      f0 s1 s2 _x _x0 _x1 _x2 _x3 __ __
    | R_merge_2 (s1, s2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, s2', p,
                 x, d) ->
      f1 s1 s2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ s2' p __ x d __

    (** val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key*'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rec f f0 f1 _ _ _ = function
    | R_merge_0 (s1, s2) -> f s1 s2 __
    | R_merge_1 (s1, s2, _x, _x0, _x1, _x2, _x3) ->
      f0 s1 s2 _x _x0 _x1 _x2 _x3 __ __
    | R_merge_2 (s1, s2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, s2', p,
                 x, d) ->
      f1 s1 s2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ s2' p __ x d __

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove

    (** val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rect x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rec x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key*'elt)

    (** val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key*'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rect f f0 f1 _ _ _ = function
    | R_concat_0 (m1, m2) -> f m1 m2 __
    | R_concat_1 (m1, m2, _x, _x0, _x1, _x2, _x3) ->
      f0 m1 m2 _x _x0 _x1 _x2 _x3 __ __
    | R_concat_2 (m1, m2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, m2', xd) ->
      f1 m1 m2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ m2' xd __

    (** val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key*'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rec f f0 f1 _ _ _ = function
    | R_concat_0 (m1, m2) -> f m1 m2 __
    | R_concat_1 (m1, m2, _x, _x0, _x1, _x2, _x3) ->
      f0 m1 m2 _x _x0 _x1 _x2 _x3 __ __
    | R_concat_2 (m1, m2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, m2', xd) ->
      f1 m1 m2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ m2' xd __

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    (** val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rect x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 r0 _res r1) rl o rr __

    (** val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rec x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 r0 _res r1) rl o rr __

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    (** val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rect f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)

    (** val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rec f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)

    type ('elt, 'x0, 'x) coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'x0 tree
    | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
       * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt

    (** val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key*'a1) list **)

    let rec flatten_e = function
    | End -> []
    | More (x, e0, t1, r) -> (x,e0)::(app (elements t1) (flatten_e r))
   end
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty m =
    Raw.is_empty (this m)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add x e m =
    Raw.add x e (this m)

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove x m =
    Raw.remove x (this m)

  (** val mem : key -> 'a1 t -> bool **)

  let mem x m =
    Raw.mem x (this m)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find x m =
    Raw.find x (this m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Raw.map f (this m)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    Raw.mapi f (this m)

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 f m m' =
    Raw.map2 f (this m) (this m')

  (** val elements : 'a1 t -> (key*'a1) list **)

  let elements m =
    Raw.elements (this m)

  (** val cardinal : 'a1 t -> int **)

  let cardinal m =
    Raw.cardinal (this m)

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    Raw.fold f (this m) i

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    Raw.equal cmp (this m) (this m')
 end

module Make =
 functor (X:OrderedType) ->
 IntMake(Z_as_Int)(X)

module SAT =
 struct
  type 'a coq_Finite = ('a list, __) sigT

  type 'a coq_EqDec = 'a -> 'a -> bool

  type 'a coq_Symbol = { finite : 'a coq_Finite; eq_dec : 'a coq_EqDec }

  (** val finite : 'a1 coq_Symbol -> 'a1 coq_Finite **)

  let finite symbol =
    symbol.finite

  (** val eq_dec : 'a1 coq_Symbol -> 'a1 coq_EqDec **)

  let eq_dec symbol =
    symbol.eq_dec

  type 'a coq_Mapping = 'a -> bool

  type 'a coq_Formula =
  | FTop
  | FBottom
  | Literal of 'a
  | And of 'a coq_Formula * 'a coq_Formula
  | Or of 'a coq_Formula * 'a coq_Formula
  | Neg of 'a coq_Formula

  (** val coq_Formula_rect :
      'a1 coq_Symbol -> 'a2 -> 'a2 -> ('a1 -> 'a2) -> ('a1 coq_Formula -> 'a2
      -> 'a1 coq_Formula -> 'a2 -> 'a2) -> ('a1 coq_Formula -> 'a2 -> 'a1
      coq_Formula -> 'a2 -> 'a2) -> ('a1 coq_Formula -> 'a2 -> 'a2) -> 'a1
      coq_Formula -> 'a2 **)

  let rec coq_Formula_rect s f f0 f1 f2 f3 f4 = function
  | FTop -> f
  | FBottom -> f0
  | Literal y -> f1 y
  | And (f6, f7) ->
    f2 f6 (coq_Formula_rect s f f0 f1 f2 f3 f4 f6) f7
      (coq_Formula_rect s f f0 f1 f2 f3 f4 f7)
  | Or (f6, f7) ->
    f3 f6 (coq_Formula_rect s f f0 f1 f2 f3 f4 f6) f7
      (coq_Formula_rect s f f0 f1 f2 f3 f4 f7)
  | Neg f6 -> f4 f6 (coq_Formula_rect s f f0 f1 f2 f3 f4 f6)

  (** val coq_Formula_rec :
      'a1 coq_Symbol -> 'a2 -> 'a2 -> ('a1 -> 'a2) -> ('a1 coq_Formula -> 'a2
      -> 'a1 coq_Formula -> 'a2 -> 'a2) -> ('a1 coq_Formula -> 'a2 -> 'a1
      coq_Formula -> 'a2 -> 'a2) -> ('a1 coq_Formula -> 'a2 -> 'a2) -> 'a1
      coq_Formula -> 'a2 **)

  let rec coq_Formula_rec s f f0 f1 f2 f3 f4 = function
  | FTop -> f
  | FBottom -> f0
  | Literal y -> f1 y
  | And (f6, f7) ->
    f2 f6 (coq_Formula_rec s f f0 f1 f2 f3 f4 f6) f7
      (coq_Formula_rec s f f0 f1 f2 f3 f4 f7)
  | Or (f6, f7) ->
    f3 f6 (coq_Formula_rec s f f0 f1 f2 f3 f4 f6) f7
      (coq_Formula_rec s f f0 f1 f2 f3 f4 f7)
  | Neg f6 -> f4 f6 (coq_Formula_rec s f f0 f1 f2 f3 f4 f6)

  (** val clause_size : 'a1 coq_Symbol -> 'a1 coq_Formula -> int **)

  let rec clause_size s = function
  | And (f, f0) -> add (clause_size s f) (clause_size s f0)
  | Or (f, f0) -> max (clause_size s f) (clause_size s f0)
  | Neg f -> clause_size s f
  | _ -> 1

  type 'a decision_procedure =
  | SAT
  | UNSAT

  (** val decision_procedure_rect :
      'a1 coq_Symbol -> 'a1 coq_Formula -> (__ -> 'a2) -> (__ -> 'a2) -> 'a1
      decision_procedure -> 'a2 **)

  let decision_procedure_rect _ _ f0 f1 = function
  | SAT -> f0 __
  | UNSAT -> f1 __

  (** val decision_procedure_rec :
      'a1 coq_Symbol -> 'a1 coq_Formula -> (__ -> 'a2) -> (__ -> 'a2) -> 'a1
      decision_procedure -> 'a2 **)

  let decision_procedure_rec _ _ f0 f1 = function
  | SAT -> f0 __
  | UNSAT -> f1 __

  type 'a decision_procedure_fun = 'a coq_Formula -> 'a decision_procedure

  (** val evaluate :
      'a1 coq_Symbol -> 'a1 coq_Formula -> 'a1 coq_Mapping -> bool **)

  let rec evaluate s f m =
    match f with
    | FTop -> true
    | FBottom -> false
    | Literal y -> m y
    | And (f0, f1) -> if evaluate s f0 m then evaluate s f1 m else false
    | Or (f0, f1) -> if evaluate s f0 m then true else evaluate s f1 m
    | Neg f0 -> negb (evaluate s f0 m)

  (** val partial_eval_and :
      'a1 coq_Symbol -> 'a1 coq_Formula -> 'a1 coq_Formula -> 'a1 coq_Formula **)

  let partial_eval_and _ f f' =
    match f with
    | FTop ->
      (match f' with
       | FTop -> FTop
       | FBottom -> FBottom
       | _ -> And (f, f'))
    | FBottom -> FBottom
    | _ -> (match f' with
            | FBottom -> FBottom
            | _ -> And (f, f'))

  (** val partial_eval_or :
      'a1 coq_Symbol -> 'a1 coq_Formula -> 'a1 coq_Formula -> 'a1 coq_Formula **)

  let partial_eval_or _ f f' =
    match f with
    | FTop -> FTop
    | FBottom ->
      (match f' with
       | FTop -> FTop
       | FBottom -> FBottom
       | _ -> Or (f, f'))
    | _ -> (match f' with
            | FTop -> FTop
            | _ -> Or (f, f'))

  (** val partial_eval_neg :
      'a1 coq_Symbol -> 'a1 coq_Formula -> 'a1 coq_Formula **)

  let partial_eval_neg _ f = match f with
  | FTop -> FBottom
  | FBottom -> FTop
  | _ -> Neg f

  (** val is_norm : 'a1 coq_Symbol -> 'a1 coq_Formula -> bool **)

  let is_norm _ = function
  | FTop -> true
  | FBottom -> true
  | _ -> false

  (** val partial_evaluate :
      'a1 coq_Symbol -> 'a1 coq_Formula -> ('a1 -> bool option) -> 'a1
      coq_Formula **)

  let rec partial_evaluate s f m =
    match f with
    | Literal y ->
      let o = m y in
      (match o with
       | Some b -> if b then FTop else FBottom
       | None -> Literal y)
    | And (f0, f1) ->
      partial_eval_and s (partial_evaluate s f0 m) (partial_evaluate s f1 m)
    | Or (f0, f1) ->
      partial_eval_or s (partial_evaluate s f0 m) (partial_evaluate s f1 m)
    | Neg f0 -> partial_eval_neg s (partial_evaluate s f0 m)
    | x -> x

  (** val mapping_is_partially_defined :
      'a1 coq_Symbol -> ('a1 -> 'a2 option) -> ('a1 -> ('a2, __) sigT) -> 'a1
      -> 'a2 **)

  let mapping_is_partially_defined _ _ x x0 =
    let s = x x0 in let ExistT (x1, _) = s in x1

  (** val get_literals : 'a1 coq_Symbol -> 'a1 coq_Formula -> 'a1 list **)

  let rec get_literals s = function
  | Literal y -> y::[]
  | And (f0, f1) -> app (get_literals s f0) (get_literals s f1)
  | Or (f0, f1) -> app (get_literals s f0) (get_literals s f1)
  | Neg f0 -> get_literals s f0
  | _ -> []

  (** val get_truth_table : int -> bool list list **)

  let rec get_truth_table n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> []::[])
      (fun n0 ->
      let iHn = get_truth_table n0 in
      app (map (fun x -> true::x) iHn) (map (fun x -> false::x) iHn))
      n

  (** val total_mapping : 'a1 coq_Symbol -> 'a1 coq_Mapping -> bool list **)

  let total_mapping s m =
    map m (projT1 s.finite)

  (** val zip_function :
      'a1 coq_EqDec -> 'a1 list -> 'a2 list -> 'a1 -> 'a2 option **)

  let rec zip_function eq_dec0 h h' x =
    match h with
    | [] -> None
    | x0::xs ->
      (match h' with
       | [] -> None
       | y::ys ->
         if is_left (eq_dec0 x0 x)
         then Some y
         else zip_function eq_dec0 xs ys x)

  type ('a, 'b) coq_R_zip_function =
  | R_zip_function_0 of 'a list * 'b list * 'a
  | R_zip_function_1 of 'a list * 'b list * 'b * 'b list * 'a
  | R_zip_function_2 of 'a list * 'b list * 'a * 'a list * 'a
  | R_zip_function_3 of 'a list * 'b list * 'a * 'a list * 'b * 'b list * 'a
  | R_zip_function_4 of 'a list * 'b list * 'a * 'a list * 'b * 'b list * 
     'a * 'b option * ('a, 'b) coq_R_zip_function

  (** val coq_R_zip_function_rect :
      'a1 coq_EqDec -> ('a1 list -> 'a2 list -> __ -> __ -> 'a1 -> 'a3) ->
      ('a1 list -> 'a2 list -> __ -> 'a2 -> 'a2 list -> __ -> 'a1 -> 'a3) ->
      ('a1 list -> 'a2 list -> 'a1 -> 'a1 list -> __ -> __ -> 'a1 -> 'a3) ->
      ('a1 list -> 'a2 list -> 'a1 -> 'a1 list -> __ -> 'a2 -> 'a2 list -> __
      -> 'a1 -> __ -> 'a3) -> ('a1 list -> 'a2 list -> 'a1 -> 'a1 list -> __
      -> 'a2 -> 'a2 list -> __ -> 'a1 -> __ -> 'a2 option -> ('a1, 'a2)
      coq_R_zip_function -> 'a3 -> 'a3) -> 'a1 list -> 'a2 list -> 'a1 -> 'a2
      option -> ('a1, 'a2) coq_R_zip_function -> 'a3 **)

  let rec coq_R_zip_function_rect eq_dec0 f f0 f1 f2 f3 _ _ _ _ = function
  | R_zip_function_0 (h, h', _x) -> f h h' __ __ _x
  | R_zip_function_1 (h, h', _x, _x0, _x1) -> f0 h h' __ _x _x0 __ _x1
  | R_zip_function_2 (h, h', x, xs, _x) -> f1 h h' x xs __ __ _x
  | R_zip_function_3 (h, h', x, xs, y, ys, a') ->
    f2 h h' x xs __ y ys __ a' __
  | R_zip_function_4 (h, h', x, xs, y, ys, a', _res, r0) ->
    f3 h h' x xs __ y ys __ a' __ _res r0
      (coq_R_zip_function_rect eq_dec0 f f0 f1 f2 f3 xs ys a' _res r0)

  (** val coq_R_zip_function_rec :
      'a1 coq_EqDec -> ('a1 list -> 'a2 list -> __ -> __ -> 'a1 -> 'a3) ->
      ('a1 list -> 'a2 list -> __ -> 'a2 -> 'a2 list -> __ -> 'a1 -> 'a3) ->
      ('a1 list -> 'a2 list -> 'a1 -> 'a1 list -> __ -> __ -> 'a1 -> 'a3) ->
      ('a1 list -> 'a2 list -> 'a1 -> 'a1 list -> __ -> 'a2 -> 'a2 list -> __
      -> 'a1 -> __ -> 'a3) -> ('a1 list -> 'a2 list -> 'a1 -> 'a1 list -> __
      -> 'a2 -> 'a2 list -> __ -> 'a1 -> __ -> 'a2 option -> ('a1, 'a2)
      coq_R_zip_function -> 'a3 -> 'a3) -> 'a1 list -> 'a2 list -> 'a1 -> 'a2
      option -> ('a1, 'a2) coq_R_zip_function -> 'a3 **)

  let rec coq_R_zip_function_rec eq_dec0 f f0 f1 f2 f3 _ _ _ _ = function
  | R_zip_function_0 (h, h', _x) -> f h h' __ __ _x
  | R_zip_function_1 (h, h', _x, _x0, _x1) -> f0 h h' __ _x _x0 __ _x1
  | R_zip_function_2 (h, h', x, xs, _x) -> f1 h h' x xs __ __ _x
  | R_zip_function_3 (h, h', x, xs, y, ys, a') ->
    f2 h h' x xs __ y ys __ a' __
  | R_zip_function_4 (h, h', x, xs, y, ys, a', _res, r0) ->
    f3 h h' x xs __ y ys __ a' __ _res r0
      (coq_R_zip_function_rec eq_dec0 f f0 f1 f2 f3 xs ys a' _res r0)

  (** val double2_list_ind :
      'a3 -> ('a2 -> 'a2 list -> 'a3) -> ('a1 -> 'a1 list -> 'a3) -> ('a1 ->
      'a2 -> 'a1 list -> 'a2 list -> 'a3 -> 'a3) -> 'a1 list -> 'a2 list ->
      'a3 **)

  let rec double2_list_ind hnil_l2 hl1_nil hind x l1 l2 =
    match l1 with
    | [] -> (match l2 with
             | [] -> hnil_l2
             | y::l -> hl1_nil y l)
    | y::l ->
      (match l2 with
       | [] -> hind y l
       | y0::l0 -> x y y0 l l0 (double2_list_ind hnil_l2 hl1_nil hind x l l0))

  (** val completness_zip_func :
      'a1 coq_EqDec -> 'a1 list -> 'a2 list -> 'a1 -> 'a2 **)

  let completness_zip_func eq_dec' h h' x =
    double2_list_ind (fun _ _ _ -> assert false (* absurd case *))
      (fun _ _ _ _ _ -> assert false (* absurd case *)) (fun _ _ _ _ _ ->
      assert false (* absurd case *)) (fun x1 x2 _ _ x0 x3 _ _ ->
      let s = eq_dec' x1 x3 in
      if s
      then internal_eq_rew_r_dep x1 x3 (fun _ _ _ -> x2) __ __ __
      else x0 x3 __ __) h h' x __ __

  (** val partial_evaluate_by_table_truth :
      'a1 coq_Symbol -> 'a1 coq_Formula -> bool list -> 'a1 coq_Formula **)

  let partial_evaluate_by_table_truth s f a =
    let o = zip_function s.eq_dec (nodup s.eq_dec (projT1 s.finite)) a in
    partial_evaluate s f o

  (** val brute_force :
      'a1 coq_Symbol -> 'a1 coq_Formula -> 'a1 coq_Formula list **)

  let brute_force s f =
    let l = get_truth_table (length (nodup s.eq_dec (projT1 s.finite))) in
    let rec f0 = function
    | [] -> (partial_evaluate_by_table_truth s f [])::[]
    | y::l1 -> (partial_evaluate_by_table_truth s f y)::(f0 l1)
    in f0 l

  (** val coq_R_brute_force_rect :
      'a1 coq_Symbol -> 'a1 coq_Formula -> 'a2 -> 'a1 coq_Formula list -> 'a2 **)

  let coq_R_brute_force_rect _ _ f _ =
    f

  (** val coq_R_brute_force_rec :
      'a1 coq_Symbol -> 'a1 coq_Formula -> 'a2 -> 'a1 coq_Formula list -> 'a2 **)

  let coq_R_brute_force_rec _ _ f _ =
    f

  (** val list_mapping :
      'a1 coq_Symbol -> ('a1 -> bool option) -> 'a1 list -> 'a1 -> bool option **)

  let list_mapping s m l x =
    match find (fun y -> is_left (s.eq_dec x y)) l with
    | Some x0 -> m x0
    | None -> None

  (** val mimimal_symbol_mapping :
      'a1 coq_Symbol -> 'a1 coq_Formula -> ('a1 -> bool option) -> 'a1 ->
      bool option **)

  let mimimal_symbol_mapping s f m =
    list_mapping s m (get_literals s f)

  (** val nth : 'a1 list -> t0 -> 'a1 **)

  let rec nth l h =
    match l with
    | [] -> assert false (* absurd case *)
    | y::l0 ->
      (match h with
       | F1 n -> solution_left (length l0) (fun _ -> y) n (nth l0)
       | FS (n, t1) ->
         solution_left (length l0) (fun h0 iHxs -> iHxs h0) n t1 (nth l0))

  (** val from_truth_table : 'a1 coq_Symbol -> t0 -> bool list **)

  let from_truth_table s h =
    nth (get_truth_table (length (nodup s.eq_dec (projT1 s.finite)))) h

  type 'a coq_CLiteral =
  | CProp of 'a
  | CNeg of 'a
  [@@deriving show]

  (** val coq_CLiteral_rect :
      'a1 coq_Symbol -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 coq_CLiteral ->
      'a2 **)

  let coq_CLiteral_rect _ f f0 = function
  | CProp a -> f a
  | CNeg a -> f0 a

  (** val coq_CLiteral_rec :
      'a1 coq_Symbol -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 coq_CLiteral ->
      'a2 **)

  let coq_CLiteral_rec _ f f0 = function
  | CProp a -> f a
  | CNeg a -> f0 a

  (** val eq_Cliteral : 'a1 coq_Symbol -> 'a1 coq_CLiteral coq_EqDec **)

  let eq_Cliteral s x y =
    match x with
    | CProp a -> (match y with
                  | CProp a0 -> s.eq_dec a a0
                  | CNeg _ -> false)
    | CNeg a -> (match y with
                 | CProp _ -> false
                 | CNeg a0 -> s.eq_dec a a0)

  type 'a coq_Clause = 'a coq_CLiteral list

  type 'a coq_CNF = 'a coq_Clause list

  (** val coq_CLiteral_to_Formula :
      'a1 coq_Symbol -> 'a1 coq_CLiteral -> 'a1 coq_Formula **)

  let coq_CLiteral_to_Formula _ = function
  | CProp a -> Literal a
  | CNeg a -> Neg (Literal a)

  (** val coq_Clause_to_Formula :
      'a1 coq_Symbol -> 'a1 coq_Clause -> 'a1 coq_Formula **)

  let rec coq_Clause_to_Formula s = function
  | [] -> FBottom
  | y::l -> Or ((coq_CLiteral_to_Formula s y), (coq_Clause_to_Formula s l))

  (** val coq_CNF_to_Formula :
      'a1 coq_Symbol -> 'a1 coq_CNF -> 'a1 coq_Formula **)

  let rec coq_CNF_to_Formula s = function
  | [] -> FTop
  | y::l -> And ((coq_Clause_to_Formula s y), (coq_CNF_to_Formula s l))

  (** val get_symbol_cliteral : 'a1 coq_Symbol -> 'a1 coq_CLiteral -> 'a1 **)

  let get_symbol_cliteral _ __top_assumption_ =
    let _evar_0_ = fun x -> x in
    let _evar_0_0 = fun x -> x in
    (match __top_assumption_ with
     | CProp a -> _evar_0_ a
     | CNeg a -> _evar_0_0 a)

  (** val succ : int -> int -> int **)

  let succ _ h =
    h

  (** val fill : int -> int list **)

  let rec fill n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0::[])
      (fun n0 -> (n0 + 1)::(map (succ n0) (fill n0)))
      n

  (** val coq_NatSymbol : int -> int coq_Symbol **)

  let coq_NatSymbol n =
    { finite = (ExistT ((fill n), __)); eq_dec = Nat.eq_dec }

  type 'a coq_Clauses = { unassigned : 'a coq_Clause; top : 'a coq_Clause;
                          bottom : 'a coq_Clause }

  (** val unassigned : 'a1 coq_Symbol -> 'a1 coq_Clauses -> 'a1 coq_Clause **)

  let unassigned _ c =
    c.unassigned

  (** val top : 'a1 coq_Symbol -> 'a1 coq_Clauses -> 'a1 coq_Clause **)

  let top _ c =
    c.top

  (** val bottom : 'a1 coq_Symbol -> 'a1 coq_Clauses -> 'a1 coq_Clause **)

  let bottom _ c =
    c.bottom

  (** val agroup_clauses :
      'a1 coq_Symbol -> 'a1 coq_Clause -> ('a1 -> bool option) -> 'a1
      coq_Clauses **)

  let rec agroup_clauses s c m =
    match c with
    | [] -> { unassigned = []; top = []; bottom = [] }
    | c0::ls ->
      (match c0 with
       | CProp s0 ->
         let { unassigned = x; top = y; bottom = z0 } = agroup_clauses s ls m
         in
         (match m s0 with
          | Some b ->
            if b
            then { unassigned = x; top = ((CProp s0)::y); bottom = z0 }
            else { unassigned = x; top = y; bottom = ((CProp s0)::z0) }
          | None -> { unassigned = ((CProp s0)::x); top = y; bottom = z0 })
       | CNeg s0 ->
         let { unassigned = x; top = y; bottom = z0 } = agroup_clauses s ls m
         in
         (match m s0 with
          | Some b ->
            if b
            then { unassigned = x; top = y; bottom = ((CNeg s0)::z0) }
            else { unassigned = x; top = ((CNeg s0)::y); bottom = z0 }
          | None -> { unassigned = ((CNeg s0)::x); top = y; bottom = z0 }))

  (** val inverse : 'a1 coq_Symbol -> 'a1 coq_CLiteral -> bool **)

  let inverse _ = function
  | CProp _ -> true
  | CNeg _ -> false

  (** val inverse' : 'a1 coq_Symbol -> 'a1 coq_CLiteral -> bool -> bool **)

  let inverse' _ = function
  | CProp _ -> (fun x -> x)
  | CNeg _ -> negb

  (** val get_units_candidate :
      'a1 coq_Symbol -> 'a1 coq_Clause -> ('a1 -> bool option) -> 'a1
      coq_CLiteral option **)

  let get_units_candidate s c m =
    let c0 = agroup_clauses s c m in
    let { unassigned = unassigned0; top = top0; bottom = _ } = c0 in
    (match unassigned0 with
     | [] -> None
     | c1::l ->
       (match l with
        | [] -> (match top0 with
                 | [] -> Some c1
                 | _::_ -> None)
        | _::_ -> None))

  (** val is_none : 'a1 option -> bool **)

  let is_none = function
  | Some _ -> false
  | None -> true

  (** val append :
      'a1 coq_Symbol -> ('a1 -> bool option) -> 'a1 -> bool option -> 'a1 ->
      bool option **)

  let append s m y v x =
    if is_left (s.eq_dec x y) then v else m x

  (** val search_pivot_clause :
      'a1 coq_Symbol -> 'a1 coq_CNF -> ('a1 -> bool option) -> 'a1
      coq_CLiteral option **)

  let rec search_pivot_clause s cnf m =
    match cnf with
    | [] -> None
    | y::l ->
      let o = get_units_candidate s y m in
      (match o with
       | Some c -> Some c
       | None -> search_pivot_clause s l m)

  (** val try_or :
      'a1 coq_Symbol -> 'a1 coq_Formula -> 'a1 coq_Formula -> 'a1 coq_Formula **)

  let try_or _ f f' =
    match f with
    | FTop -> FTop
    | _ -> (match f' with
            | FTop -> FTop
            | _ -> f)

  (** val backtrack :
      'a1 coq_Symbol -> 'a1 coq_Formula -> ('a1 -> bool option) -> 'a1
      coq_CLiteral list -> 'a1 coq_Formula **)

  let backtrack s f m = function
  | [] -> FBottom
  | y::_ ->
    try_or s
      (partial_evaluate s f
        (append s m (get_symbol_cliteral s y) (Some true)))
      (partial_evaluate s f
        (append s m (get_symbol_cliteral s y) (Some false)))

  module type SymbolOrder =
   sig
    type coq_A

    type t = coq_A

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  module DLLP =
   functor (M:SymbolOrder) ->
   struct
    module MNat = Make(M)

    type coq_Context = bool MNat.t

    (** val coq_EmptyContext : coq_Context **)

    let coq_EmptyContext =
      MNat.empty

    type 'a coq_StepStatus =
    | Stop of coq_Context
    | Continue of coq_Context

    (** val coq_StepStatus_rect :
        'a1 coq_Symbol -> (coq_Context -> 'a2) -> (coq_Context -> 'a2) -> 'a1
        coq_StepStatus -> 'a2 **)

    let coq_StepStatus_rect _ f f0 = function
    | Stop c -> f c
    | Continue c -> f0 c

    (** val coq_StepStatus_rec :
        'a1 coq_Symbol -> (coq_Context -> 'a2) -> (coq_Context -> 'a2) -> 'a1
        coq_StepStatus -> 'a2 **)

    let coq_StepStatus_rec _ f f0 = function
    | Stop c -> f c
    | Continue c -> f0 c

    (** val get_ctx_from_step :
        M.coq_A coq_Symbol -> M.coq_A coq_StepStatus -> coq_Context **)

    let get_ctx_from_step _ = function
    | Stop c -> c
    | Continue c -> c

    (** val propagate :
        M.coq_A coq_Symbol -> M.coq_A coq_CLiteral -> coq_Context ->
        coq_Context **)

    let propagate _ literal ctx =
      match literal with
      | CProp a -> MNat.add a true ctx
      | CNeg a -> MNat.add a false ctx

    (** val coq_ContextMaps : coq_Context -> M.t -> bool option **)

    let coq_ContextMaps ctx k =
      MNat.find k ctx

    (** val step_unit :
        M.coq_A coq_Symbol -> M.coq_A coq_CNF -> coq_Context -> M.coq_A
        coq_StepStatus **)

      
    let step_unit s cnf ctx =
      let o = search_pivot_clause s cnf (coq_ContextMaps ctx) in
      (match o with
       | Some c -> Continue (propagate s c ctx)
       | None -> Stop ctx)

    (** val backtrack :
        'a1 coq_Symbol -> 'a1 coq_Formula -> ('a1 -> bool option) -> 'a1
        coq_CLiteral list -> 'a1 coq_Formula **)

    let backtrack s f m = function
    | [] -> FBottom
    | y::_ ->
      try_or s
        (partial_evaluate s f
          (append s m (get_symbol_cliteral s y) (Some true)))
        (partial_evaluate s f
          (append s m (get_symbol_cliteral s y) (Some false)))
   end
 end


exception CoqProp of string
exception Unreachable

open SAT
module IntCompare = struct
  type coq_A = int 
  type t = coq_A

  let compare : t -> t -> t compare0 = fun x y -> 
    match Int.compare x y with
       | 0 -> EQ
       |(-1) -> LT
       | 1 -> GT
       | _ -> raise Unreachable

  let eq_dec : t -> t -> bool = fun x y -> x == y
end

open DLLP(IntCompare)

let parse_dimacs (input: string) =
  let lines = String.split_on_char '\n' input in
  
  (* Helper to split string on whitespace *)
  let split_whitespace s =
    s |> String.trim |> String.split_on_char ' ' 
    |> List.filter (fun s -> String.length s > 0)
  in
  
  (* Convert string to literal *)
  let to_literal n =
    let num = int_of_string n in
    if num > 0 then CProp num
    else CNeg (-num)
  in
  
  (* Process a line containing clause numbers *)
  let process_clause_line nums =
    let rec process_nums acc = function
      | [] -> List.rev acc
      | "0"::rest -> List.rev acc
      | num::rest -> process_nums ((to_literal num)::acc) rest
    in
    process_nums [] nums
  in
  
  (* Main processing loop *)
  let rec process_lines clauses n = function
    | [] -> (List.rev clauses, n)
    | line::rest ->
        let tokens = split_whitespace line in
        match tokens with
        | [] -> process_lines clauses n rest  (* Empty line *)
        | "c"::_ -> process_lines clauses n rest  (* Comment line *)
        | "p"::"cnf"::digits::xs -> process_lines clauses (int_of_string digits) rest  (* Header line *)
        | nums -> 
            let clause_tokens = 
              List.filter (fun s -> 
                try let _ = int_of_string s in true
                with Failure _ -> false) nums
            in
            if clause_tokens = [] then
              process_lines clauses n rest
            else
              let new_clause = process_clause_line clause_tokens in
              if new_clause = [] then
                process_lines clauses n rest
              else
                process_lines (new_clause::clauses) n rest
  in
  process_lines [] 0 lines

  let rec pretty_print_formula to_string formula =
    match formula with
    | FTop -> "⊤"
    | FBottom -> "⊥"
    | Literal x -> to_string x
    | And (f1, f2) -> 
        "(" ^ (pretty_print_formula to_string f1) ^ 
        " ∧ " ^ 
        (pretty_print_formula to_string f2) ^ ")"
    | Or (f1, f2) -> 
        "(" ^ (pretty_print_formula to_string f1) ^ 
        " ∨ " ^ 
        (pretty_print_formula to_string f2) ^ ")"
    | Neg f -> "¬" ^ (pretty_print_formula to_string f)

module IntSet = Set.Make(Int)

let find_pure_literal formula ctx  =
  (* Use a hash table to track literal occurrences *)
  let lit_count = Hashtbl.create 32 in
  let neg_count = Hashtbl.create 32 in
  
  (* Count occurrences of literals and their negations *)
  let count_literal = function
    | CProp v -> 
        Hashtbl.replace lit_count v 
          (1 + (try Hashtbl.find lit_count v with Not_found -> 0))
    | CNeg v ->
        Hashtbl.replace neg_count v 
          (1 + (try Hashtbl.find neg_count v with Not_found -> 0))
  in
  
  List.iter count_literal formula;
  
  (* Find first pure literal *)
  let result = ref None in
  try
    Hashtbl.iter (fun v count ->
      let neg_occurs = try Hashtbl.find neg_count v with Not_found -> 0 in
      if neg_occurs = 0 then
        match !result with
        | None -> 
          if (is_none (MNat.find v ctx)) then
            result := Some (CProp v)
          else ()
        | Some _ -> raise Exit  (* More than one pure literal found *)
    ) lit_count;
    
    Hashtbl.iter (fun v count ->
      let pos_occurs = try Hashtbl.find lit_count v with Not_found -> 0 in
      if pos_occurs = 0 then
        match !result with
        | None -> 
          if (is_none (MNat.find v ctx)) then
            result := Some (CNeg v)
          else ()
        | Some _ -> raise Exit  (* More than one pure literal found *)
    ) neg_count;
    
    !result
  with Exit -> None  (* Return None if multiple pure literals found *)

(**Attention this only works when the formula has no polarity higher than 3, example (neg (neg (neg l)))*)
let step_pure_literal s cnf ctx =
  let o = find_pure_literal cnf ctx in
  match o with
    | None -> Stop ctx
    | Some (CNeg x) -> Continue (MNat.add x false ctx)
    | Some (CProp x) -> Continue (MNat.add x true ctx)

type status =
  |Sat 
  |Unsat
  |Incomplete

let rec apply_until_stop step s cnf ctx =
  match (step s cnf ctx) with
    |(Continue x) -> apply_until_stop step s cnf x
    |(Stop x) -> x

let rec check_sat (formula: 'a coq_Formula) : status =
  match formula with
  | FTop -> Sat
  | FBottom -> Unsat
  | Literal _ -> Incomplete
  | And (f1, f2) ->
      (match check_sat f1, check_sat f2 with
      | Unsat, _ | _, Unsat -> Unsat
      | Sat, Sat -> Sat
      | _, _ -> Incomplete)
  | Or (f1, f2) ->
      (match check_sat f1, check_sat f2 with
      | Sat, _ | _, Sat -> Sat
      | Unsat, Unsat -> Unsat
      | _, _ -> Incomplete)
  | Neg f ->
      match check_sat f with
      | Sat -> Unsat
      | Unsat -> Sat
      | Incomplete -> Incomplete

(* Cache for memoization *)
let memo_table = Hashtbl.create 1024

(* Helper function to create a unique key for memoization *)
let create_memo_key formula ctx =
  let ctx_str = MNat.fold (fun k v acc -> 
    acc ^ string_of_int k ^ (if v then "T" else "F")
  ) ctx "" in
  Hashtbl.hash (formula, ctx_str)

(* Improved DPLL function with memoization and optimizations *)
let rec dpll s cnf formula ctx = 
  (* Check memoization table first *)
  let memo_key = create_memo_key formula ctx in
  match Hashtbl.find_opt memo_table memo_key with
  | Some result -> result
  | None ->
    (* Apply unit propagation and pure literal elimination *)
    let ctx = apply_until_stop step_unit s cnf ctx in
    let ctx = apply_until_stop step_pure_literal s (List.flatten cnf) ctx in
    let formula = partial_evaluate s formula (coq_ContextMaps ctx) in

    let result = match check_sat formula with
      | Sat -> 
          (true, ctx)
      | Unsat -> 
          (false, ctx)
      | Incomplete -> 
          (* Choose next variable using heuristic *)
          let next_var = choose_next_variable s ctx cnf in
          (* Try true first, then false *)
          let (res, r) = dpll s cnf formula (MNat.add next_var true ctx) in
          let (res', r') = dpll s cnf formula (MNat.add next_var false ctx) in
          if res then (res, r) else (res', r)
    in 
    (* Store result in memoization table *)
    Hashtbl.add memo_table memo_key result;
    result

(* Heuristic function to choose the next variable *)
and choose_next_variable s ctx cnf =
  let vars = projT1 (finite s) in
  let unassigned = List.filter (fun x -> is_none (MNat.find x ctx)) vars in
  
  (* Count variable occurrences *)
  let var_counts = Hashtbl.create (List.length unassigned) in
  List.iter (fun clause ->
    List.iter (fun lit ->
      match lit with
      | CProp v | CNeg v ->
          if is_none (MNat.find v ctx) then
            Hashtbl.replace var_counts v 
              (1 + (try Hashtbl.find var_counts v with Not_found -> 0))
    ) clause
  ) cnf;
  
  (* Choose variable with highest occurrence count *)
  match unassigned with
  | [] -> failwith "No unassigned variables"
  | hd::_ ->
      List.fold_left (fun best_var var ->
        let count1 = try Hashtbl.find var_counts best_var with Not_found -> 0 in
        let count2 = try Hashtbl.find var_counts var with Not_found -> 0 in
        if count2 > count1 then var else best_var
      ) hd unassigned

(* Helper function to clear memoization table *)
let clear_dpll_cache () =
  Hashtbl.clear memo_table

let read_file file =
  try
    Ok(In_channel.with_open_bin file In_channel.input_all)
  with
  | Sys_error msg -> 
    Error(msg)
    
let runDllp formula n = 
  let (cnf, instance) = (formula,
      {finite = ExistT (List.init n (fun x -> x + 1), __); eq_dec = fun x y -> x == y}) in
  (* print_newline (); *)
  clear_dpll_cache ();
  let (r, ctx) = dpll instance cnf (coq_CNF_to_Formula __ cnf) (MNat.empty) in
  print_string (Printf.sprintf "s %s\n" (if r then "SATISFIABLE" else "UNSATISFIABLE"));
  if r then
    let mapping = List.map (fun v -> if (is_none (MNat.find v ctx)) then v * - 1 else v) (projT1 instance.finite) in
    print_string (Printf.sprintf "s %s" (String.concat " " (List.map string_of_int mapping)));
  else
    print_string ""

let main = 
  let f = read_file Sys.argv.(1) in
  match f with
      |Ok(problem) -> 
        let (formula, n) = parse_dimacs problem in
        runDllp formula n
      |Error(msg) -> Printf.printf "Error reading directory: %s\n" msg