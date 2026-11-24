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

The check `chk` runs over the nondecreasing tuples of at most six residues with the right sum. The sums `S_t`, one for
each unit `t`, are packed in base 1024, and the packed values of the residues are read from a table. `chk_sound` proves
that a successful check covers every balanced list of that length. It is evaluated by the kernel (`decide +kernel`),
split by the first element for six residues.
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

theorem forallFrom_complete {lo n : Nat} {p : Nat → Bool} (h : ∀ i, lo ≤ i → i < lo + n → p i = true) :
    forallFrom lo n p = true := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih =>
    simp only [forallFrom, Bool.and_eq_true]
    exact ⟨h lo (Nat.le_refl _) (by omega), ih (fun i h1 h2 => h i (by omega) (by omega))⟩

/-- The numbers `V 1, …, V 43`, 256 bits each. -/
def table : Nat := 0x403014070240d03c1104c1505c1906c1d07c23094270a42b00000000000000008060280e0481a078220982a008060280e0481a078220982a0000000000000000c0903c1506c2700407034130641f0942b0141105c1d08c29000000000000000100c0501c0900804018080280100c0501c090080401808028000000000000000140f064230041507c2901c1106c2500c0d05c2b024130742700000000000000018120782a028220080e06826018120782a028220080e068260000000000000001c1508c0504c030441f0040f0742b0341b0a41909c0905c2500000000000000020180a00c070100800405024020180a00c070100800405024000000000000000241b004130941d00c1509c0d07c0505c2903c070642b04423000000000000000281e0181a0082a04826038220281e0181a0082a04826038220000000000000002c2102c2102c0b0840b0840b0840b0840b0842102c2102c21000000000000000302404028050180101c020200302404028050180101c020200000000000000003427054030742504c0106c0908c110ac1901c0f0a4170141f000000000000000382a0680a09806088120081e0382a0680a09806088120081e0000000000000003c0107c1100c13014230540709417024270642906c0d0ac1d00000000000000040040901803020050080a01c040040901803020050080a01c00000000000000044070a41f0540108c1903c0509c1d04c090ac17034030941b000000000000000480a008260780e0182a0881a0480a008260780e0182a0881a0000000000000004c0d01c0109c1b0540f024030a42307417044050ac2507c19000000000000000501003008010280902007018050100300801028090200701800000000000000054130440f0340901c0500c010ac2909c2508c1f0741b0641700000000000000058160581605816058160581605816058160581605816058160000000000000005c1906c1d07c23094270a42b00403014070240d03c1104c15000000000000000601c080240a0040200c040140601c080240a0040200c04014000000000000000641f0942b0141105c1d08c2900c0903c1506c27004070341300000000000000068220a8060381e0980202812068220a8060381e09802028120000000000000006c2500c0d05c2b02413074270140f064230041507c2901c110000000000000007028020140800c060240101007028020140800c0602401010000000000000000742b0341b0a41909c0905c2501c1508c0504c030441f0040f000000000000000780204822018260281a0a80e0780204822018260281a0a80e0000000000000007c0505c2903c070642b044230241b004130941d00c1509c0d000000000000000800807004060140a0100900c0800807004060140a0100900c000000000000000840b0840b0842102c2102c2102c2102c2102c0b0840b0840b000000000000000880e098120a802068060780a0880e098120a802068060780a0000000000000008c110ac1901c0f0a4170141f03427054030742504c0106c090000000000000009014010200401c030280600809014010200401c03028060080000000000000009417024270642906c0d0ac1d03c0107c1100c130142305407000000000000000981a038020880a0a81e048060981a038020880a0a81e048060000000000000009c1d04c090ac17034030941b044070a41f0540108c1903c05000000000000000a020060100202407014030040a02006010020240701403004000000000000000a42307417044050ac2507c1904c0d01c0109c1b0540f02403000000000000000a8260881e068120380a018020a8260881e068120380a01802000000000000000ac2909c2508c1f0741b06417054130440f0340901c0500c010000000000000000000000000000000000000000000000000000000000000000

/-- `V x`, read in the table. -/
def look (x : Nat) : Nat := Nat.mod (Nat.shiftRight table (Nat.mul 256 x)) 115792089237316195423570985008687907853269984665640564039457584007913129639936

theorem look_eq : ∀ x : Fin 44, look x.val = V x.val := by decide +kernel

/-- `chk n lo s acc A T`: every nondecreasing list of `n` residues from `lo` on, with sum `s` and packed sums `T - acc`,
has, together with `A`, an even number of residues of the chosen order. The bounds of the loop leave only the first
elements that can be completed. -/
def chk : Nat → Nat → Nat → Nat → List Nat → Nat → Bool
  | 0, _, _, acc, A, T => cond (Nat.beq acc T) (Nat.beq (Nat.mod (nu A) 2) 0) true
  | n + 1, lo, s, acc, A, T =>
    let b := Nat.sub s (Nat.mul 43 n)
    let a := cond (Nat.ble lo b) b lo
    forallFrom a (Nat.sub (Nat.succ (Nat.div s (Nat.succ n))) a) (fun x =>
      chk n x (Nat.sub s x) (Nat.add acc (look x)) (x :: A) T)

theorem chk_sound (n : Nat) : ∀ (lo s acc T : Nat) (A L : List Nat), chk n lo s acc A T = true → L.length = n →
    L.Pairwise (· ≤ ·) → (∀ x ∈ L, lo ≤ x ∧ x ≤ 43) → L.sum = s → acc + pk (stv L) = T →
    nu (L.reverse ++ A) % 2 = 0 := by
  induction n with
  | zero =>
    intro lo s acc T A L h hl _ _ hs hT
    have : L = [] := List.eq_nil_of_length_eq_zero hl
    subst this
    rw [pk_stv_nil, Nat.add_zero] at hT
    subst hT
    have h' : cond (Nat.beq acc acc) (Nat.beq (Nat.mod (nu A) 2) 0) true = true := h
    rw [Nat.beq_refl] at h'
    exact Nat.eq_of_beq_eq_true h'
  | succ n ih =>
    intro lo s acc T A L h hl hp hr hs hT
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
      have hdiv : x ≤ s / (n + 1) := by
        rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_succ]
        omega
      have h' : forallFrom (cond (Nat.ble lo (s - 43 * n)) (s - 43 * n) lo)
          (s / (n + 1) + 1 - cond (Nat.ble lo (s - 43 * n)) (s - 43 * n) lo)
          (fun x => chk n x (s - x) (acc + look x) (x :: A) T) = true := h
      have ha : cond (Nat.ble lo (s - 43 * n)) (s - 43 * n) lo ≤ x := by
        cases hc : Nat.ble lo (s - 43 * n)
        · exact hx.1
        · show s - 43 * n ≤ x
          omega
      have hin := forallFrom_sound h' x ha (by omega)
      rw [pk_stv_cons, ← look_eq ⟨x, by omega⟩] at hT
      have := ih x (s - x) (acc + look x) T (x :: A) L' hin hl' (List.pairwise_cons.mp hp).2
        (fun y hy => ⟨hpx y hy, (hr y (List.mem_cons_of_mem _ hy)).2⟩) (by omega)
        (by rw [Nat.add_assoc]; exact hT)
      rw [List.reverse_cons, List.append_assoc]
      exact this

theorem chk0 : chk 0 1 0 0 [] 0 = true := by decide +kernel
theorem chk1 : chk 1 1 22 0 [] 34557807403419145710579829942820701129509741801780491081750 = true := by decide +kernel
theorem chk2 : chk 2 1 44 0 [] 69115614806838291421159659885641402259019483603560982163500 = true := by decide +kernel
theorem chk3 : chk 3 1 66 0 [] 103673422210257437131739489828462103388529225405341473245250 = true := by decide +kernel
theorem chk4 : chk 4 1 88 0 [] 138231229613676582842319319771282804518038967207121964327000 = true := by decide +kernel
theorem chk5 : chk 5 1 110 0 [] 172789037017095728552899149714103505647548709008902455408750 = true := by decide +kernel

theorem chk6_1 : chk 5 1 131 67541734393237265599056984832161175420739463112396377164801 [1] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_2 : chk 5 2 130 65967853979636239776954309778735471188920871842801522841602 [2] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_3 : chk 5 3 129 64393973566035214014799874506197020511748606859616724198403 [3] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_4 : chk 5 4 128 62820093152434249519746495411984955503155215833420110245892 [4] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_5 : chk 5 5 127 61246212738896022596122939764313363592673790026982899072005 [5] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_6 : chk 5 6 126 59672332325294996833968447320787365176820137318262786508806 [6] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_7 : chk 5 7 125 58098451976000104381474853798524980546424586882415273726983 [7] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_8 : chk 5 8 124 56524571562399078559430664776913812561067731811906657214472 [8] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_9 : chk 5 9 123 54950756998215824378379568942519257811913613455556296600585 [9] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_10 : chk 5 10 122 53376876584677597454756013239125508853118650715359705856010 [10] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_11 : chk 5 11 121 51802996171076632959761120232450137139300532822008709284875 [11] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_12 : chk 5 12 120 50229115757475607197548198872374993167352994705978293260300 [12] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_13 : chk 5 13 119 48655235408180653418063738307448114869826129434042843569165 [13] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_14 : chk 5 14 118 47081354994579688923010416328501440551600589199622163965966 [14] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_15 : chk 5 15 117 45574904384839561169044267412844241124333739484573600842767 [15] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_16 : chk 5 16 116 44001023971238535347000078391233073138976884414064984330256 [16] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_17 : chk 5 17 115 42427143557637570851946756468008555869064881113403684297745 [17] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_18 : chk 5 18 114 40853328993454316670895660577891844071597225823293944113170 [18] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_19 : chk 5 19 113 39279448644159362891411257128230356464438211343134428771347 [19] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_20 : chk 5 20 112 37705568230621135967787644309571216815275397811161903677460 [20] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_21 : chk 5 21 111 36131687817020171532682504996246405361328333071375345404949 [21] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel
theorem chk6_22 : chk 5 22 110 34557807403419145710579829942820701129509741801780491081750 [22] 207346844420514874263478979656924206777058450810682946490500 = true := by decide +kernel

theorem chk6 : chk 6 1 132 0 [] 207346844420514874263478979656924206777058450810682946490500 = true := by
  show forallFrom 1 22 (fun x => chk 5 x (Nat.sub 132 x) (Nat.add 0 (look x)) [x] 207346844420514874263478979656924206777058450810682946490500) = true
  simp only [forallFrom, Bool.and_eq_true]
  exact ⟨chk6_1, chk6_2, chk6_3, chk6_4, chk6_5, chk6_6, chk6_7, chk6_8, chk6_9, chk6_10, chk6_11, chk6_12, chk6_13, chk6_14, chk6_15, chk6_16, chk6_17, chk6_18, chk6_19, chk6_20, chk6_21, chk6_22, trivial⟩

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
  have key : ∀ n, n ≤ 6 → chk n 1 (22 * n) 0 [] (22 * n * R) = true := by
    have hR : R = 1570809427428142986844537724673668233159533718262749594625 := by decide +kernel
    rw [hR]
    intro n hn
    match n, hn with
    | 0, _ => exact chk0
    | 1, _ => exact chk1
    | 2, _ => exact chk2
    | 3, _ => exact chk3
    | 4, _ => exact chk4
    | 5, _ => exact chk5
    | 6, _ => exact chk6
  have hp := chk_sound L'.length 1 (22 * L'.length) 0 (22 * L'.length * R) [] L' (key _ (by omega)) rfl hsort' hr'
    hsum hT
  rw [List.append_nil] at hp
  rw [← nu_perm ((List.reverse_perm L').trans hperm)]
  exact hp

end FermatLength.List44
