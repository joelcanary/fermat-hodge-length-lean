/-
Copyright 2026 Joel Cruz Cabrera.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# No balanced list of at most six residues modulo 44 has an odd number of elements of order 11

The check `chk` runs over the ordered tuples of at most six residues, with the sums `S_t` (one for each unit `t`)
packed in base 1024, and `chk_sound` proves that a successful check covers every balanced list of that length. It is
evaluated by the kernel (`decide +kernel`), split by the first element for five and six residues.
-/

@[expose] public section

namespace FermatLength.List44

/-- The units modulo 44, as a literal list. -/
def U : List Nat := [1, 3, 5, 7, 9, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 35, 37, 39, 41, 43]

/-- `S_t(L) = Σ_{x ∈ L} (t·x mod 44)`. -/
def St (t : Nat) (L : List Nat) : Nat := (L.map (fun x => t * x % 44)).sum

/-- Balanced: `S_t(L) = 22·|L|` for every unit `t`. For a zero-free multiset of even length this is Shioda's Hodge
condition; it is linear, so it makes sense for every length. -/
def balanced (L : List Nat) : Bool := U.all (fun t => St t L == 22 * L.length)

/-- `1` if `x` has order 11 in `ℤ/44` (a nonzero multiple of 4), otherwise `0`. -/
def o11 (x : Nat) : Nat := if x % 4 == 0 && x % 44 != 0 then 1 else 0

/-- `ν_11(L)`: the number of elements of order 11 in `L` (its parity is the invariant). -/
def nu (L : List Nat) : Nat := (L.map o11).sum

/-- Nonzero residues, represented in `1..43`. -/
def inRange (L : List Nat) : Prop := ∀ x ∈ L, 1 ≤ x ∧ x ≤ 43


theorem sum_perm {L₁ L₂ : List Nat} (h : L₁.Perm L₂) : L₁.sum = L₂.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [List.sum_cons, ih]
  | swap x y l => simp [List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => omega

theorem map_sum_perm (f : Nat → Nat) {L₁ L₂ : List Nat} (h : L₁.Perm L₂) :
    (L₁.map f).sum = (L₂.map f).sum := sum_perm (h.map f)

theorem balanced_spec {L : List Nat} : balanced L = true ↔ ∀ t ∈ U, St t L = 22 * L.length := by
  simp [balanced, List.all_eq_true]

def forallFrom (lo : Nat) : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p lo && forallFrom (lo + 1) n p

theorem forallFrom_sound {lo n : Nat} {p : Nat → Bool} (h : forallFrom lo n p = true) :
    ∀ i, lo ≤ i → i < lo + n → p i = true := by
  induction n generalizing lo with
  | zero => intro i h1 h2; omega
  | succ n ih =>
    simp only [forallFrom, Bool.and_eq_true] at h
    intro i h1 h2
    by_cases hi : i = lo
    · subst hi; exact h.1
    · exact ih h.2 i (by omega) (by omega)

def pk : List Nat → Nat
  | [] => 0
  | a :: as => a + 1024 * pk as

def stv (L : List Nat) : List Nat := U.map (fun t => St t L)
def V (x : Nat) : Nat := pk (stv [x])
def R : Nat := pk (U.map (fun _ => 1))

theorem pk_add (f g : Nat → Nat) : ∀ us : List Nat,
    pk (us.map (fun t => f t + g t)) = pk (us.map f) + pk (us.map g)
  | [] => rfl
  | u :: us => by simp only [List.map_cons, pk, pk_add f g us]; omega

theorem pk_const (c : Nat) : ∀ us : List Nat, pk (us.map (fun _ => c)) = c * pk (us.map (fun _ => 1))
  | [] => rfl
  | u :: us => by simp only [List.map_cons, pk, pk_const c us, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]

theorem St_cons (t x : Nat) (L : List Nat) : St t (x :: L) = St t [x] + St t L := by
  simp [St, List.sum_cons]

theorem pk_stv_cons (x : Nat) (L : List Nat) : pk (stv (x :: L)) = V x + pk (stv L) := by
  unfold V stv
  rw [show U.map (fun t => St t (x :: L)) = U.map (fun t => St t [x] + St t L) from
    List.map_congr_left (fun t _ => St_cons t x L)]
  exact pk_add _ _ U

theorem pk_stv_nil : pk (stv []) = 0 := by decide

def chk : Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, s, acc, c, T => if s == 0 then (!(acc == T) || c % 2 == 0) else true
  | n + 1, lo, s, acc, c, T =>
    forallFrom lo (44 - lo) (fun x =>
      if Nat.ble (x * (n + 1)) s && Nat.ble s (x + 43 * n) then chk n x (s - x) (acc + V x) (c + o11 x) T else true)

theorem sum_ge {x : Nat} : ∀ {L : List Nat}, (∀ y ∈ L, x ≤ y) → x * L.length ≤ L.sum
  | [], _ => by simp
  | y :: L, h => by
    have h1 := h y (List.mem_cons_self ..)
    have h2 := sum_ge (L := L) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [List.length_cons, List.sum_cons, Nat.mul_succ]
    omega

theorem sum_le : ∀ {L : List Nat}, (∀ y ∈ L, y ≤ 43) → L.sum ≤ 43 * L.length
  | [], _ => by simp
  | y :: L, h => by
    have h1 := h y (List.mem_cons_self ..)
    have h2 := sum_le (L := L) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [List.length_cons, List.sum_cons]
    omega

theorem chk_sound (n : Nat) : ∀ (lo s acc c T : Nat) (L : List Nat), chk n lo s acc c T = true →
    L.length = n →
    L.Pairwise (· ≤ ·) → (∀ x ∈ L, lo ≤ x ∧ x ≤ 43) → L.sum = s → acc + pk (stv L) = T → (c + nu L) % 2 = 0 := by
  induction n with
  | zero =>
    intro lo s acc c T L h hl _ _ hs hT
    have : L = [] := List.eq_nil_of_length_eq_zero hl
    subst this
    simp only [List.sum_nil] at hs
    subst hs
    rw [pk_stv_nil, Nat.add_zero] at hT
    subst hT
    simpa [chk, nu] using h
  | succ n ih =>
    intro lo s acc c T L h hl hp hr hs hT
    cases L with
    | nil => exact absurd hl (by simp)
    | cons x L' =>
      have hx := hr x (List.mem_cons_self ..)
      have hpx : ∀ y ∈ L', x ≤ y := (List.pairwise_cons.mp hp).1
      have hl' : L'.length = n := by simpa using hl
      have hs' : x + L'.sum = s := by simpa using hs
      have hge := sum_ge hpx
      rw [hl'] at hge
      have hle := sum_le (L := L') (fun y hy => (hr y (List.mem_cons_of_mem _ hy)).2)
      rw [hl'] at hle
      have hin := forallFrom_sound h x hx.1 (by omega)
      have hcond : (Nat.ble (x * (n + 1)) s && Nat.ble s (x + 43 * n)) = true := by
        simp only [Bool.and_eq_true, Nat.ble_eq]
        constructor
        · rw [Nat.mul_succ]; omega
        · omega
      try dsimp only at hin
      simp only [hcond, ↓reduceIte] at hin
      rw [pk_stv_cons] at hT
      have := ih x (s - x) (acc + V x) (c + o11 x) T L' hin hl' (List.pairwise_cons.mp hp).2
        (fun y hy => ⟨hpx y hy, (hr y (List.mem_cons_of_mem _ hy)).2⟩) (by omega) (by omega)
      simp only [nu, List.map_cons, List.sum_cons] at this ⊢
      omega

theorem forallFrom_complete {lo n : Nat} {p : Nat → Bool} (h : ∀ i, lo ≤ i → i < lo + n → p i = true) :
    forallFrom lo n p = true := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih =>
    simp only [forallFrom, Bool.and_eq_true]
    exact ⟨h lo (Nat.le_refl _) (by omega), ih (fun i h1 h2 => h i (by omega) (by omega))⟩
theorem chk0 : chk 0 1 0 0 0 (22 * 0 * R) = true := by decide +kernel
theorem chk1 : chk 1 1 22 0 0 (22 * 1 * R) = true := by decide +kernel
theorem chk2 : chk 2 1 44 0 0 (22 * 2 * R) = true := by decide +kernel
theorem chk3 : chk 3 1 66 0 0 (22 * 3 * R) = true := by decide +kernel
theorem chk4 : chk 4 1 88 0 0 (22 * 4 * R) = true := by decide +kernel

theorem chk5_1 : chk 4 1 109 (0 + V 1) (0 + o11 1) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_2 : chk 4 2 108 (0 + V 2) (0 + o11 2) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_3 : chk 4 3 107 (0 + V 3) (0 + o11 3) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_4 : chk 4 4 106 (0 + V 4) (0 + o11 4) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_5 : chk 4 5 105 (0 + V 5) (0 + o11 5) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_6 : chk 4 6 104 (0 + V 6) (0 + o11 6) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_7 : chk 4 7 103 (0 + V 7) (0 + o11 7) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_8 : chk 4 8 102 (0 + V 8) (0 + o11 8) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_9 : chk 4 9 101 (0 + V 9) (0 + o11 9) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_10 : chk 4 10 100 (0 + V 10) (0 + o11 10) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_11 : chk 4 11 99 (0 + V 11) (0 + o11 11) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_12 : chk 4 12 98 (0 + V 12) (0 + o11 12) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_13 : chk 4 13 97 (0 + V 13) (0 + o11 13) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_14 : chk 4 14 96 (0 + V 14) (0 + o11 14) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_15 : chk 4 15 95 (0 + V 15) (0 + o11 15) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_16 : chk 4 16 94 (0 + V 16) (0 + o11 16) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_17 : chk 4 17 93 (0 + V 17) (0 + o11 17) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_18 : chk 4 18 92 (0 + V 18) (0 + o11 18) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_19 : chk 4 19 91 (0 + V 19) (0 + o11 19) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_20 : chk 4 20 90 (0 + V 20) (0 + o11 20) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_21 : chk 4 21 89 (0 + V 21) (0 + o11 21) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5_22 : chk 4 22 88 (0 + V 22) (0 + o11 22) (22 * 5 * R) = true := by
  decide +kernel

theorem chk5 : chk 5 1 110 0 0 (22 * 5 * R) = true := by
  show forallFrom 1 43 _ = true
  apply forallFrom_complete
  intro x h1 h2
  match x, h1, h2 with
  | 1, _, _ => exact chk5_1
  | 2, _, _ => exact chk5_2
  | 3, _, _ => exact chk5_3
  | 4, _, _ => exact chk5_4
  | 5, _, _ => exact chk5_5
  | 6, _, _ => exact chk5_6
  | 7, _, _ => exact chk5_7
  | 8, _, _ => exact chk5_8
  | 9, _, _ => exact chk5_9
  | 10, _, _ => exact chk5_10
  | 11, _, _ => exact chk5_11
  | 12, _, _ => exact chk5_12
  | 13, _, _ => exact chk5_13
  | 14, _, _ => exact chk5_14
  | 15, _, _ => exact chk5_15
  | 16, _, _ => exact chk5_16
  | 17, _, _ => exact chk5_17
  | 18, _, _ => exact chk5_18
  | 19, _, _ => exact chk5_19
  | 20, _, _ => exact chk5_20
  | 21, _, _ => exact chk5_21
  | 22, _, _ => exact chk5_22
  | x + 23, _, _ =>
    split
    · rename_i h
      simp only [Bool.and_eq_true, Nat.ble_eq] at h
      omega
    · rfl

theorem chk6_1 : chk 5 1 131 (0 + V 1) (0 + o11 1) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_2 : chk 5 2 130 (0 + V 2) (0 + o11 2) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_3 : chk 5 3 129 (0 + V 3) (0 + o11 3) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_4 : chk 5 4 128 (0 + V 4) (0 + o11 4) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_5 : chk 5 5 127 (0 + V 5) (0 + o11 5) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_6 : chk 5 6 126 (0 + V 6) (0 + o11 6) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_7 : chk 5 7 125 (0 + V 7) (0 + o11 7) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_8 : chk 5 8 124 (0 + V 8) (0 + o11 8) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_9 : chk 5 9 123 (0 + V 9) (0 + o11 9) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_10 : chk 5 10 122 (0 + V 10) (0 + o11 10) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_11 : chk 5 11 121 (0 + V 11) (0 + o11 11) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_12 : chk 5 12 120 (0 + V 12) (0 + o11 12) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_13 : chk 5 13 119 (0 + V 13) (0 + o11 13) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_14 : chk 5 14 118 (0 + V 14) (0 + o11 14) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_15 : chk 5 15 117 (0 + V 15) (0 + o11 15) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_16 : chk 5 16 116 (0 + V 16) (0 + o11 16) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_17 : chk 5 17 115 (0 + V 17) (0 + o11 17) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_18 : chk 5 18 114 (0 + V 18) (0 + o11 18) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_19 : chk 5 19 113 (0 + V 19) (0 + o11 19) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_20 : chk 5 20 112 (0 + V 20) (0 + o11 20) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_21 : chk 5 21 111 (0 + V 21) (0 + o11 21) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6_22 : chk 5 22 110 (0 + V 22) (0 + o11 22) (22 * 6 * R) = true := by
  decide +kernel

theorem chk6 : chk 6 1 132 0 0 (22 * 6 * R) = true := by
  show forallFrom 1 43 _ = true
  apply forallFrom_complete
  intro x h1 h2
  match x, h1, h2 with
  | 1, _, _ => exact chk6_1
  | 2, _, _ => exact chk6_2
  | 3, _, _ => exact chk6_3
  | 4, _, _ => exact chk6_4
  | 5, _, _ => exact chk6_5
  | 6, _, _ => exact chk6_6
  | 7, _, _ => exact chk6_7
  | 8, _, _ => exact chk6_8
  | 9, _, _ => exact chk6_9
  | 10, _, _ => exact chk6_10
  | 11, _, _ => exact chk6_11
  | 12, _, _ => exact chk6_12
  | 13, _, _ => exact chk6_13
  | 14, _, _ => exact chk6_14
  | 15, _, _ => exact chk6_15
  | 16, _, _ => exact chk6_16
  | 17, _, _ => exact chk6_17
  | 18, _, _ => exact chk6_18
  | 19, _, _ => exact chk6_19
  | 20, _, _ => exact chk6_20
  | 21, _, _ => exact chk6_21
  | 22, _, _ => exact chk6_22
  | x + 23, _, _ =>
    split
    · rename_i h
      simp only [Bool.and_eq_true, Nat.ble_eq] at h
      omega
    · rfl

theorem St_one {L : List Nat} (hr : inRange L) : St 1 L = L.sum := by
  unfold St
  induction L with
  | nil => rfl
  | cons x L ih =>
    have hx := hr x (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons]
    rw [ih (fun y hy => hr y (List.mem_cons_of_mem _ hy))]
    rw [Nat.one_mul, Nat.mod_eq_of_lt (by omega)]

theorem balanced_perm {L₁ L₂ : List Nat} (h : L₁.Perm L₂) : balanced L₁ = balanced L₂ := by
  unfold balanced St
  rw [h.length_eq]
  congr 1
  funext t
  rw [map_sum_perm _ h]

theorem nu_perm {L₁ L₂ : List Nat} (h : L₁.Perm L₂) : nu L₁ = nu L₂ := map_sum_perm o11 h

theorem short_balanced {L : List Nat} (hr : inRange L) (hl : L.length ≤ 6) (he : balanced L = true) : nu L % 2 = 0 := by
  let le : Nat → Nat → Bool := fun a b => decide (a ≤ b)
  let L' := L.mergeSort le
  have hperm : L'.Perm L := List.mergeSort_perm L le
  have hsort : L'.Pairwise (fun a b => le a b = true) :=
    List.pairwise_mergeSort (le := le) (by intro a b c h1 h2; simp [le] at *; omega)
      (by intro a b; simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) L
  have hsort' : L'.Pairwise (· ≤ ·) := hsort.imp (by intro a b h; simpa [le] using h)
  have hr' : ∀ x ∈ L', 1 ≤ x ∧ x ≤ 43 := fun x hx => hr x (hperm.mem_iff.mp hx)
  have he' : balanced L' = true := by rw [balanced_perm hperm]; exact he
  have hl' : L'.length = L.length := hperm.length_eq
  have hsum : L'.sum = 22 * L'.length := by
    have := (balanced_spec.mp he') 1 (by decide)
    rw [St_one hr'] at this
    exact this
  have hT : 0 + pk (stv L') = 22 * L'.length * R := by
    rw [Nat.zero_add]
    unfold stv
    rw [List.map_congr_left (fun t ht => (balanced_spec.mp he') t ht), pk_const]
    rfl
  have key : ∀ n, n ≤ 6 → chk n 1 (22 * n) 0 0 (22 * n * R) = true := by
    intro n hn
    match n, hn with
    | 0, _ => exact chk0
    | 1, _ => exact chk1
    | 2, _ => exact chk2
    | 3, _ => exact chk3
    | 4, _ => exact chk4
    | 5, _ => exact chk5
    | 6, _ => exact chk6
  have hp := chk_sound L'.length 1 (22 * L'.length) 0 0 (22 * L'.length * R) L' (key _ (by omega)) rfl hsort' hr'
    hsum hT
  rw [← nu_perm hperm]
  omega


end FermatLength.List44
