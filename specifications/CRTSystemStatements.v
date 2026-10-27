(* Full signed-i64 mathematical contracts, separate from the legacy envelope. *)
From Coq Require Import ZArith List Bool Lia Permutation.
From CRT Require Import CRTStatements.
Import ListNotations.
Open Scope Z_scope.
Module FullWidth.
Definition MAX : Z := i64_max.
Definition moduli (m n : Z) : Prop := 1 <= m <= MAX /\ 1 <= n <= MAX.
Definition domain (a m b n : Z) : Prop :=
  moduli m n /\ 0 <= a < m /\ 0 <= b < n.
Definition T_normalize : Prop :=
  forall z d : Z, word z -> 1 <= d <= MAX ->
    let r := Z.rem z d in
    let result := if r <? 0 then r + d else r in
    result = z mod d /\ 0 <= result < d /\ word r /\ word result.

(* Euclid: initialization (m,n), transition (r0,r1) -> (r1,r0 mod r1).
   The second remainder is a natural-number termination measure. *)
Definition gcd_inv (m n r0 r1 : Z) : Prop :=
  1 <= r0 <= MAX /\ 0 <= r1 <= MAX /\
  Z.gcd r0 r1 = Z.gcd m n.

Definition T_gcd_init : Prop :=
  forall m n : Z, moduli m n -> gcd_inv m n m n.
Definition T_gcd_step : Prop :=
  forall m n r0 r1 : Z, gcd_inv m n r0 r1 -> 0 < r1 ->
    gcd_inv m n r1 (r0 mod r1) /\ 0 <= r0 mod r1 < r1 /\
    (Z.to_nat (r0 mod r1) < Z.to_nat r1)%nat.
Definition T_gcd_exit : Prop :=
  forall m n r0 : Z, gcd_inv m n r0 0 -> r0 = Z.gcd m n.

Definition eea_inputs (A B : Z) : Prop := 1 <= B < A /\ A <= MAX.
Definition T_eea_init : Prop :=
  forall A B : Z, eea_inputs A B -> eea_inv A B (eea_init A B).
Definition T_eea_step : Prop :=
  forall (A B : Z) (e : eea_state),
    eea_inputs A B -> eea_inv A B e -> 0 < r1 e ->
    eea_inv A B (eea_step e) /\
    0 <= r1 (eea_step e) < r1 e /\
    (Z.to_nat (r1 (eea_step e)) < Z.to_nat (r1 e))%nat.
Definition T_eea_step_bounds : Prop :=
  forall (A B : Z) (e : eea_state),
    eea_inputs A B -> eea_inv A B e -> 0 < r1 e ->
    let q := r0 e / r1 e in
    1 <= q <= A /\ 0 <= q * r1 e <= A /\
    Z.abs (q * s1 e) <= B /\ Z.abs (s0 e - q * s1 e) <= B /\
    Z.abs (q * t1 e) <= A /\ Z.abs (t0 e - q * t1 e) <= A /\
    word (q * s1 e) /\ word (s0 e - q * s1 e) /\
    word (q * t1 e) /\ word (t0 e - q * t1 e).
Definition T_eea_exit : Prop :=
  forall (A B : Z) (e : eea_state),
    eea_inputs A B -> eea_inv A B e -> r1 e = 0 ->
    r0 e = Z.gcd A B /\ A * s0 e + B * t0 e = Z.gcd A B /\
    (Z.gcd A B = 1 ->
      0 <= t0 e mod A < A /\ congruent A (B * (t0 e mod A)) 1).

Definition T_construct : Prop :=
  forall a m b n : Z, domain a m b n -> compatible a m b n ->
    let g := Z.gcd m n in
    let m1 := m / g in
    let n1 := n / g in
    (n1 = 1 -> canonical a m b n a) /\
    (1 < n1 -> forall u : Z,
       0 <= u < n1 -> congruent n1 (m1 * u) 1 ->
       canonical a m b n (a + m * (((b - a) / g * u) mod n1))).


Definition add_mod (x y d : Z) : Z :=
  if d-y <=? x then x-(d-y) else x+y.
Definition T_add_mod : Prop := forall x y d,
  1 <= d <= MAX -> 0 <= x < d -> 0 <= y < d ->
  add_mod x y d = (x+y) mod d /\ 0 <= add_mod x y d < d /\
  word (d-y) /\ word (add_mod x y d) /\
  (x < d-y -> word (x+y)).
Record mul_state := { acc : Z; factor : Z; remaining : Z }.
Definition mul_step (d : Z) (e : mul_state) : mul_state :=
  {| acc := if remaining e mod 2 =? 1 then add_mod (acc e) (factor e) d else acc e;
     factor := add_mod (factor e) (factor e) d;
     remaining := remaining e / 2 |}.
Fixpoint mul_loop (fuel : nat) (d : Z) (e : mul_state) : Z :=
  match fuel with
  | O => acc e
  | S k => if 0 <? remaining e then mul_loop k d (mul_step d e) else acc e
  end.
Definition mul_mod (x y d : Z) :=
  mul_loop 64 d {| acc:=0; factor:=x; remaining:=y |}.
Definition mul_inv (product d : Z) (e : mul_state) : Prop :=
  0 <= acc e < d /\ 0 <= factor e < d /\ 0 <= remaining e /\
  congruent d (acc e + factor e * remaining e) product.
Definition T_mul_step : Prop := forall product d e,
  1 <= d <= MAX -> mul_inv product d e -> 0 < remaining e ->
  mul_inv product d (mul_step d e) /\
  0 <= remaining (mul_step d e) < remaining e /\
  word (acc (mul_step d e)) /\ word (factor (mul_step d e)) /\
  (remaining e <= MAX -> word (remaining (mul_step d e))).
Definition T_mul_mod : Prop := forall x y d,
  1 <= d <= MAX -> 0 <= x < d -> 0 <= y < d ->
  mul_mod x y d = (x*y) mod d /\ 0 <= mul_mod x y d < d /\ word (mul_mod x y d).
Fixpoint gcd_loop (fuel : nat) (a b : Z) : Z :=
  match fuel with O => a | S k =>
    if 0 <? b then gcd_loop k b (a mod b) else a end.
Definition gcd_model (a b : Z) := gcd_loop (S (Z.to_nat b)) a b.
Fixpoint eea_loop (fuel : nat) (e : eea_state) : eea_state :=
  match fuel with O => e | S k =>
    if 0 <? r1 e then eea_loop k (eea_step e) else e end.
Definition inverse_model (B A : Z) :=
  t0 (eea_loop (S (Z.to_nat B)) (eea_init A B)) mod A.
Definition T_gcd_model : Prop := forall a b, moduli a b -> gcd_model a b = Z.gcd a b.
Definition T_inverse_model : Prop := forall A B,
  eea_inputs A B -> Z.gcd A B = 1 ->
  0 <= inverse_model B A < A /\ congruent A (B * inverse_model B A) 1.
Definition T_lcm_guard : Prop := forall m n, moduli m n ->
  ((m / Z.gcd m n > MAX / n) <-> MAX < Z.lcm m n) /\
  (m / Z.gcd m n <= MAX / n -> word ((m / Z.gcd m n)*n)).
Definition T_construct_bounds : Prop := forall a m b n,
  domain a m b n -> compatible a m b n -> Z.lcm m n <= MAX ->
  word (b-a) /\ word ((b-a)/Z.gcd m n) /\
  (forall t, 0 <= t < n / Z.gcd m n ->
    word (m*t) /\ word (a+m*t) /\ 0 <= a+m*t < Z.lcm m n).
End FullWidth.

Module FiniteSystem.
Import FullWidth.
Definition constraint := (Z * Z)%type.
Definition positive (C : list constraint) : Prop := Forall (fun c => 0 < snd c) C.
Definition valid_entry (c : constraint) : Prop := 1 <= snd c <= MAX /\ 0 <= fst c < snd c.
Definition valid (C : list constraint) : Prop := Forall valid_entry C.
Definition Sol (C : list constraint) (x : Z) : Prop :=
  forall a m, In (a,m) C -> congruent m x a.
Fixpoint L (C : list constraint) : Z :=
  match C with [] => 1 | (_,m)::rest => Z.lcm m (L rest) end.
Definition Pairwise (C : list constraint) : Prop :=
  forall a m b n, In (a,m) C -> In (b,n) C -> compatible a m b n.
Definition Rep (C : list constraint) (r p : Z) : Prop :=
  p = L C /\ 0 <= r < p /\ forall x, Sol C x <-> congruent p x r.
Definition validb (c : constraint) : bool :=
  (1 <=? snd c) && (snd c <=? MAX) && (0 <=? fst c) && (fst c <? snd c).
Definition compatb (c d : constraint) : bool :=
  ((fst d - fst c) mod Z.gcd (snd c) (snd d) =? 0).
Fixpoint validate_loop (C : list constraint) : bool :=
  match C with [] => true | c::cs => if validb c then validate_loop cs else false end.
Fixpoint pair_row (c : constraint) (C : list constraint) : bool :=
  match C with [] => true | d::ds => if compatb c d then pair_row c ds else false end.
Fixpoint pair_loop (C : list constraint) : bool :=
  match C with [] => true | c::cs => if pair_row c cs then pair_loop cs else false end.
Inductive result := Invalid | Inconsistent | Overflow | Success (r p : Z).
Definition merge (a m b n : Z) : result :=
  if validb (a,m) && validb (b,n) then
    let g := gcd_model m n in
    if (b-a) mod g =? 0 then
      let m1 := m/g in
      if MAX/n <? m1 then Overflow else
        let n1 := n/g in
        let r := if n1 =? 1 then a else
          a + m * mul_mod (((b-a)/g) mod n1)
              (inverse_model (m1 mod n1) n1) n1 in
        Success r (m1*n)
    else Inconsistent
  else Invalid.
Fixpoint solve_fold (C : list constraint) (r p : Z) : result :=
  match C with
  | [] => Success r p
  | (a,m)::cs => match merge r p a m with
      | Success r' p' => solve_fold cs r' p'
      | error => error end
  end.
Fixpoint period_fold (C : list constraint) (p : Z) : Z :=
  match C with [] => p | (_,m)::cs =>
    let factor := p / gcd_model p m in
    if MAX/m <? factor then -3 else period_fold cs (factor*m) end.
Definition system_model (C : list constraint) : result :=
  if validate_loop C then
    if pair_loop C then solve_fold C 0 1 else Inconsistent
  else Invalid.
Definition period_model (C : list constraint) : Z :=
  if validate_loop C then
    if pair_loop C then period_fold C 1 else -1
  else -2.
Definition solve_value (q : result) : Z :=
  match q with Invalid => -2 | Inconsistent => -1 | Overflow => -3 | Success r _ => r end.
Definition period_value (q : result) : Z :=
  match q with Invalid => -2 | Inconsistent => -1 | Overflow => -3 | Success _ p => p end.
Definition batch_model (C : list constraint) (count : Z) : result :=
  if (0 <=? count) && (count <=? 16) then system_model (firstn (Z.to_nat count) C)
  else Invalid.
Definition result_post (C : list constraint) (q : result) : Prop :=
  match q with
  | Invalid => ~ valid C
  | Inconsistent => valid C /\ ~ Pairwise C
  | Overflow => valid C /\ Pairwise C /\ MAX < L C
  | Success r p => valid C /\ Pairwise C /\ p <= MAX /\ Rep C r p
  end.
Definition T_finite_existence : Prop := forall C, positive C ->
  ((exists x, Sol C x) <-> Pairwise C).
Definition T_finite_canonical : Prop := forall C, positive C -> Pairwise C ->
  exists r, Rep C r (L C) /\ forall s, Rep C s (L C) -> s=r.
Definition T_finite_all_solutions : Prop := forall C r p, Rep C r p ->
  forall x, Sol C x <-> exists k, x=r+k*p.
Definition T_period_subsystem : Prop := forall A B,
  incl A B -> (L A | L B).
Definition T_composition : Prop := forall A B r p s q,
  positive A -> positive B -> Rep A r p -> Rep B s q ->
  (forall x, Sol (A++B) x <-> solution r p s q x) /\
  L (A++B) = Z.lcm p q /\
  ((exists x, Sol (A++B) x) <-> compatible r p s q).
Definition T_scalar_model : Prop := forall a m b n,
  result_post [(a,m);(b,n)] (merge a m b n).
Definition T_finite_model : Prop := forall C, result_post C (system_model C).
Definition T_period_model : Prop := forall C,
  period_model C = period_value (system_model C).
Definition T_permutation : Prop := forall A B,
  Permutation A B -> system_model A = system_model B.
Definition T_merge_composition : Prop := forall A B r p s q,
  valid A -> valid B -> Rep A r p -> Rep B s q -> p <= MAX -> q <= MAX ->
  result_post (A++B) (merge r p s q).
Definition T_empty : Prop := system_model [] = Success 0 1.
Definition T_singleton : Prop := forall a m, valid_entry (a,m) ->
  system_model [(a,m)] = Success a m.
Definition T_duplicate : Prop := forall C c,
  In c C -> system_model (c::C) = system_model C.
(* Cursor invariants for the concrete validate/pair/fold traversals. *)
Definition validation_inv (done todo : list constraint) : Prop := valid done.
Definition pair_scan_inv (done : list constraint) (current : constraint)
    (checked pending tail : list constraint) : Prop :=
  Pairwise done /\
  (forall c d, In c done -> In d (current::checked++pending++tail) ->
    compatible (fst c) (snd c) (fst d) (snd d)) /\
  (forall d, In d checked -> compatible (fst current) (snd current) (fst d) (snd d)).
Definition fold_inv (done : list constraint) (r p : Z) : Prop := Rep done r p /\ p <= MAX.
End FiniteSystem.

Module FiniteSystemTargets.
Import FullWidth FiniteSystem.
Definition T_overflow_exact : Prop := forall C,
  system_model C = Overflow <-> valid C /\ Pairwise C /\ MAX < L C.
Definition T_summary_commutative : Prop := forall A B r p s q,
  valid A -> valid B -> Rep A r p -> Rep B s q -> p <= MAX -> q <= MAX ->
  merge r p s q = merge s q r p.
Definition T_summary_associative : Prop := forall A B C r p s q t u abv abp bcv bcp,
  valid A -> valid B -> valid C -> Rep A r p -> Rep B s q -> Rep C t u ->
  p <= MAX -> q <= MAX -> u <= MAX ->
  merge r p s q = Success abv abp -> merge s q t u = Success bcv bcp ->
  merge abv abp t u = merge r p bcv bcp.
Definition T_scan_models : Prop :=
  (forall C, validate_loop C = true <-> valid C) /\
  (forall C, positive C -> (pair_loop C = true <-> Pairwise C)) /\
  (forall (c : constraint) C, (length C < length (c::C))%nat).
Definition T_cursor_bounds : Prop := forall (count i j : Z),
  0 <= count <= 16 -> 0 <= i < count -> i+1 <= j < count ->
  0 <= i < 16 /\ 0 <= j < 16 /\ 0 <= i+1 <= 16 /\
  0 <= j+1 <= 16 /\ 0 <= 8*i <= 120 /\ 0 <= 8*j <= 120 /\
  0 <= count-(i+1) < count-i /\ 0 <= count-(j+1) < count-j.
Definition T_batch_classification : Prop := forall C count,
  length C = 16%nat ->
  ((count < 0 \/ 16 < count) -> batch_model C count = Invalid) /\
  (0 <= count <= 16 -> result_post (firstn (Z.to_nat count) C) (batch_model C count)).
End FiniteSystemTargets.

Module FiniteLoopTargets.
Import FullWidth FiniteSystem.
Definition T_prefix_fold : Prop := forall C A r p,
  valid (A++C) -> Pairwise (A++C) -> Rep A r p -> p <= MAX ->
  result_post (A++C) (solve_fold C r p).
Definition T_period_fold_equivalence : Prop := forall C A r p,
  valid (A++C) -> Pairwise (A++C) -> Rep A r p -> p <= MAX ->
  period_fold C p = period_value (solve_fold C r p).
Definition T_overflow_monotone : Prop := forall A B,
  positive B -> incl A B -> MAX < L A -> MAX < L B.
Definition T_gcd_lcm_distributive : Prop := forall a b c,
  0 <= a -> 0 <= b -> 0 <= c ->
  Z.gcd a (Z.lcm b c) = Z.lcm (Z.gcd a b) (Z.gcd a c).
End FiniteLoopTargets.

Module FullWidthMachineTargets.
Import FullWidth.
Definition T_index_arithmetic : Prop := forall count i,
  0 <= count <= 16 -> 0 <= i < count ->
  0 <= i < 16 /\ 0 <= i+1 <= 16 /\ i+1 < 2147483648 /\
  word i /\ word (i+1) /\ 0 <= 8*i <= 120 /\
  0 <= count-(i+1) < count-i.
Definition T_mul_machine_arithmetic : Prop := forall d e product,
  1 <= d <= MAX -> mul_inv product d e -> remaining e <= MAX -> 0 < remaining e ->
  word (acc e) /\ word (factor e) /\ word (remaining e) /\
  word (remaining e mod 2) /\ word (remaining e / 2) /\
  (Z.to_nat (remaining (mul_step d e)) < Z.to_nat (remaining e))%nat.
Definition T_reduction_machine_bounds : Prop := forall a m b n,
  domain a m b n ->
  let g := Z.gcd m n in
  1 <= g <= MAX /\ 1 <= m/g <= MAX /\ 1 <= n/g <= MAX /\
  word g /\ word (m/g) /\ word (n/g) /\ word (b-a) /\
  word ((b-a) mod g) /\ word ((b-a)/g).
End FullWidthMachineTargets.

Module IndexedLoopTargets.
Import FiniteSystem.
Definition active_cursor (C : list constraint) (count i : nat) : list constraint :=
  firstn (count-i) (skipn i C).
Definition T_indexed_list_bridge : Prop := forall C count i,
  (i < count <= length C)%nat ->
  active_cursor C count i = nth i C (0,1) :: active_cursor C count (S i) /\
  firstn (S i) C = firstn i C ++ [nth i C (0,1)] /\
  (count-S i < count-i)%nat.
End IndexedLoopTargets.

Module SignedArithmeticTargets.
Import FullWidth.
Definition T_signed_arithmetic_bridge : Prop := forall z d,
  word z -> 1 <= d <= MAX ->
  (Z.rem z d = 0 <-> z mod d = 0) /\
  ((d | z) -> Z.quot z d = z/d) /\
  (0 <= z -> Z.rem z d = z mod d /\ Z.quot z d = z/d).
End SignedArithmeticTargets.
