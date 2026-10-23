(* Exact proof targets over mathematical integers. These are Definitions of
   propositions, not asserted or proved theorems. No admissions or axioms.
   Elaboration checks their types, not their truth or a connection to Wasm. *)
From Coq Require Import ZArith.
Open Scope Z_scope.

Definition M : Z := 2147483647.
Definition i64_min : Z := -9223372036854775808.
Definition i64_max : Z := 9223372036854775807.
Definition word (z : Z) : Prop := i64_min <= z <= i64_max.
Definition moduli (m n : Z) : Prop := 1 <= m <= M /\ 1 <= n <= M.
Definition domain (a m b n : Z) : Prop :=
  moduli m n /\ 0 <= a < m /\ 0 <= b < n.
Definition congruent (d x a : Z) : Prop := (d | x - a).
Definition solution (a m b n x : Z) : Prop :=
  congruent m x a /\ congruent n x b.
Definition period (m n : Z) : Z := (m / Z.gcd m n) * n.
Definition compatible (a m b n : Z) : Prop := (Z.gcd m n | b - a).
Definition canonical (a m b n x : Z) : Prop :=
  0 <= x < period m n /\ solution a m b n x.

Definition T_normalization : Prop :=
  forall a m b n x : Z, 0 < m -> 0 < n ->
    (solution a m b n x <-> solution (a mod m) m (b mod n) n x).

Definition T_reduction : Prop :=
  forall m n : Z, 0 < m -> 0 < n ->
    let g := Z.gcd m n in
    0 < g /\ (g | m) /\ (g | n) /\
    0 < m / g /\ 0 < n / g /\ Z.gcd (m / g) (n / g) = 1 /\
    period m n = Z.lcm m n /\ 0 < period m n.

Definition T_generalized_CRT : Prop :=
  forall a m b n : Z, 0 < m -> 0 < n ->
    ((exists x : Z, solution a m b n x) <-> compatible a m b n).

Definition T_canonical_unique : Prop :=
  forall a m b n : Z, 0 < m -> 0 < n -> compatible a m b n ->
    exists x : Z, canonical a m b n x /\
      forall y : Z, canonical a m b n y -> y = x.

Definition T_all_solutions : Prop :=
  forall a m b n x : Z, 0 < m -> 0 < n -> solution a m b n x ->
    forall y : Z, solution a m b n y <->
      exists k : Z, y = x + k * period m n.

Definition T_incompatible : Prop :=
  forall a m b n : Z, 0 < m -> 0 < n -> ~ compatible a m b n ->
    forall x : Z, ~ solution a m b n x.

Definition T_construct : Prop :=
  forall a m b n : Z, domain a m b n -> compatible a m b n ->
    let g := Z.gcd m n in
    let m1 := m / g in
    let n1 := n / g in
    (n1 = 1 -> canonical a m b n a) /\
    (1 < n1 -> forall u : Z,
       0 <= u < n1 -> congruent n1 (m1 * u) 1 ->
       canonical a m b n (a + m * (((b - a) / g * u) mod n1))).

Definition T_normalize : Prop :=
  forall z d : Z, word z -> 1 <= d <= M ->
    let r := Z.rem z d in
    let result := if r <? 0 then r + d else r in
    result = z mod d /\ 0 <= result < d /\ word r /\ word result.

(* Euclid: initialization (m,n), transition (r0,r1) -> (r1,r0 mod r1).
   The second remainder is a natural-number termination measure. *)
Definition gcd_inv (m n r0 r1 : Z) : Prop :=
  1 <= r0 <= M /\ 0 <= r1 <= M /\
  Z.gcd r0 r1 = Z.gcd m n.

Definition T_gcd_init : Prop :=
  forall m n : Z, moduli m n -> gcd_inv m n m n.
Definition T_gcd_step : Prop :=
  forall m n r0 r1 : Z, gcd_inv m n r0 r1 -> 0 < r1 ->
    gcd_inv m n r1 (r0 mod r1) /\ 0 <= r0 mod r1 < r1 /\
    (Z.to_nat (r0 mod r1) < Z.to_nat r1)%nat.
Definition T_gcd_exit : Prop :=
  forall m n r0 : Z, gcd_inv m n r0 0 -> r0 = Z.gcd m n.

Record eea_state := {
  r0 : Z; r1 : Z; s0 : Z; s1 : Z; t0 : Z; t1 : Z
}.
Definition eea_init (A B : Z) : eea_state :=
  {| r0 := A; r1 := B; s0 := 1; s1 := 0; t0 := 0; t1 := 1 |}.
Definition eea_step (e : eea_state) : eea_state :=
  let q := r0 e / r1 e in
  {| r0 := r1 e; r1 := r0 e mod r1 e;
     s0 := s1 e; s1 := s0 e - q * s1 e;
     t0 := t1 e; t1 := t0 e - q * t1 e |}.
Definition eea_inputs (A B : Z) : Prop := 1 <= B < A /\ A <= M.
Definition eea_inv (A B : Z) (e : eea_state) : Prop :=
  0 <= r1 e /\ r1 e < r0 e /\ r0 e <= A /\
  Z.gcd (r0 e) (r1 e) = Z.gcd A B /\
  r0 e = A * s0 e + B * t0 e /\
  r1 e = A * s1 e + B * t1 e /\
  Z.abs (s0 e * t1 e - s1 e * t0 e) = 1 /\
  s0 e * s1 e <= 0 /\ t0 e * t1 e <= 0 /\
  r0 e * Z.abs (s1 e) + r1 e * Z.abs (s0 e) = B /\
  r0 e * Z.abs (t1 e) + r1 e * Z.abs (t0 e) = A /\
  Z.abs (s0 e) <= B /\ Z.abs (s1 e) <= B /\
  Z.abs (t0 e) <= A /\ Z.abs (t1 e) <= A.

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

Definition T_crt_bounds : Prop :=
  forall a m b n : Z, domain a m b n -> compatible a m b n ->
    let g := Z.gcd m n in
    let m1 := m / g in
    let n1 := n / g in
    let delta := b - a in
    1 <= g <= M /\ 1 <= m1 <= M /\ 1 <= n1 <= M /\
    Z.abs delta <= M - 1 /\ Z.abs (delta / g) <= M - 1 /\
    1 <= period m n <= M * M /\ word (period m n) /\
    (1 < n1 -> 1 <= m1 mod n1 < n1) /\
    forall u : Z, 0 <= u < n1 ->
      let product := (delta / g) * u in
      let t := product mod n1 in
      Z.abs product <= (M - 1) * (M - 1) /\ word product /\
      0 <= t < n1 /\ 0 <= m * t <= M * (M - 1) /\ word (m * t) /\
      0 <= a + m * t < period m n /\ word (a + m * t).

(* API refinement targets are predicates ON execution relations.
   Their arguments are not supplied as axioms. CRTExecutionTargets.v instantiates
   these relations with actual generated Wasm execution in a valid runtime. *)
Definition solve_post (a m b n result : Z) : Prop :=
  (~ domain a m b n /\ result = -2) \/
  (domain a m b n /\ ~ compatible a m b n /\ result = -1) \/
  (domain a m b n /\ compatible a m b n /\ canonical a m b n result).
Definition period_post (m n result : Z) : Prop :=
  (~ moduli m n /\ result = -2) \/
  (moduli m n /\ result = Z.lcm m n).
Definition total_correct (run post : Z -> Prop) : Prop :=
  (exists result : Z, run result) /\
  forall result : Z, run result -> word result /\ post result.

Definition T_solve_execution (exec : Z -> Z -> Z -> Z -> Z -> Prop) : Prop :=
  forall a m b n : Z, word a -> word m -> word b -> word n ->
    total_correct (exec a m b n) (solve_post a m b n).
Definition T_period_execution (exec : Z -> Z -> Z -> Prop) : Prop :=
  forall m n : Z, word m -> word n ->
    total_correct (exec m n) (period_post m n).
Definition T_gcd_execution (exec : Z -> Z -> Z -> Prop) : Prop :=
  forall m n : Z, moduli m n ->
    total_correct (exec m n) (fun result => result = Z.gcd m n).
Definition T_normalize_execution (exec : Z -> Z -> Z -> Prop) : Prop :=
  forall z d : Z, word z -> 1 <= d <= M ->
    total_correct (exec z d) (fun result => result = z mod d).
Definition T_inverse_execution (exec : Z -> Z -> Z -> Prop) : Prop :=
  forall A B : Z, eea_inputs A B -> Z.gcd A B = 1 ->
    total_correct (exec B A)
      (fun u => 0 <= u < A /\ congruent A (B * u) 1).
