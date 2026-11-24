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
# No balanced list of at most six residues modulo 52 has an odd number of elements of order 13

The check `chk` runs over the nondecreasing tuples of at most six residues with the right sum. The sums `S_t`, one for
each unit `t`, are packed in base 1024, and the packed values of the residues are read from a table. `chk_sound` proves
that a successful check covers every balanced list of that length. It is evaluated by the kernel (`decide +kernel`),
split by the first element for six residues.
-/

@[expose] public section

namespace FermatLength.List52

/-- The units modulo 52, as a literal list. -/
def U : List Nat := [1, 3, 5, 7, 9, 11, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 41, 43, 45, 47, 49, 51]

/-- `S_t(L) = Σ_{x ∈ L} (t·x mod 52)`. -/
def St (t : Nat) (L : List Nat) : Nat := (L.map (fun x => t * x % 52)).sum

/-- Balanced: `S_t(L) = 26·|L|` for every unit `t`. For a zero-free multiset of even length this is Shioda's Hodge
condition; it is linear, so it makes sense for every length. -/
def balanced (L : List Nat) : Bool := U.all (fun t => St t L == 26 * L.length)

/-- `1` if `x` has order 13 in `ℤ/52` (a nonzero multiple of 4), otherwise `0`. -/
def oL (x : Nat) : Nat := if x % 4 == 0 && x % 52 != 0 then 1 else 0

/-- `ν_13(L)`: the number of elements of order 13 in `L` (its parity is the invariant). -/
def nu (L : List Nat) : Nat := (L.map oL).sum

/-- Nonzero residues, represented in `1..51`. -/
def inRange (L : List Nat) : Prop := ∀ x ∈ L, 1 ≤ x ∧ x ≤ 51


theorem sum_perm {L₁ L₂ : List Nat} (h : L₁.Perm L₂) : L₁.sum = L₂.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [List.sum_cons, ih]
  | swap x y l => simp [List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => omega

theorem map_sum_perm (f : Nat → Nat) {L₁ L₂ : List Nat} (h : L₁.Perm L₂) :
    (L₁.map f).sum = (L₂.map f).sum := sum_perm (h.map f)

theorem balanced_spec {L : List Nat} : balanced L = true ↔ ∀ t ∈ U, St t L = 26 * L.length := by
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

theorem sum_le : ∀ {L : List Nat}, (∀ y ∈ L, y ≤ 51) → L.sum ≤ 51 * L.length
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

/-- The numbers `V 1, …, V 51`, 256 bits each. -/
def table : Nat := 0x403014070240b03c1104c1505c1906c1d07c2108c250a42b0b42f0c4330000008060280e04816078220982a0b832008060280e04816078220982a0b832000000c0903c1506c210b4330140b04417074230a42f0040704c1907c250ac3100000100c0501c0902c02010060200a0300100c0501c0902c02010060200a03000000140f064230b40305c210ac0102c1507c290cc0904c1d0c4070441b0942f0000018120782a0080e09832028160882e018120782a0080e09832028160882e000001c1508c3102c190040f0742b014130842f024170943306c2900c1107c2d0000020180a00405024040200c00c0702c020180a00405024040200c00c0702c00000241b0b40b0742f07c3103c210cc1108c0104c2500c15014170a4070642b00000281e0c812098060b80e088020582a0281e0c812098060b80e088020582a000002c2100c190bc110241f004170b40f09407074330542b08c0506c3104c29000003024020200101c060300502c0402803024020200101c060300502c04028000003427034270342709c0d09c0d09c0d09c0d09c0d09c0d03427034270342700000382a0482e058320081e01822028260382a0482e058320081e0182202826000003c2d05c0107c090442f064030840b0a4130c41b014230ac150cc1d01c25000004030070080a0140800c0b0180102404030070080a0140800c0b018010240000044330840f0c41f0bc1d02c2d06c090ac1901c2905c05054030941300423000004802098160182a0282e0780e0c82204802098160182a0282e0780e0c822000004c050ac1d03c010640b0c423054070b41f044030a41b0cc2505c090bc210000050080c0240600c0a01c040040b020050080c0240600c0a01c040040b02000000540b0042b0841700c2d08c1903c050bc2506c1101c3107413024330a41f00000580e018320a8220480a0082e0981e0580e018320a8220480a0082e0981e000005c1102c050cc2d0841b0540f024030c42b0941f0641301c010bc2908c1d0000060140400c020040c02c0a0240801c060140400c020040c02c0a0240801c000006417054130440f02c0901c0500c010cc310bc2d0ac29094230841f0741b00000681a0681a0681a0681a0681a0681a0681a0681a0681a0681a0681a0681a000006c1d07c2108c250a42b0b42f0c43300403014070240b03c1104c1505c19000007020090280b03001008030100501807020090280b0300100803010050180000074230a42f0040704c1907c250ac3100c0903c1506c210b4330140b044170000078260b802028120882a0c80603816078260b802028120882a0c80603816000007c290cc0904c1d0c4070441b0942f0140f064230b40305c210ac0102c1500000802c01010070280301809030020140802c010100702803018090300201400000842f024170943306c2900c1107c2d01c1508c3102c190040f0742b014130000088320381e0b80a0a8060582600812088320381e0b80a0a8060582600812000008c0104c2500c15014170a4070642b0241b0b40b0742f07c3103c210cc110000090040602c03020050280201c0c010090040602c03020050280201c0c010000009407074330542b08c0506c3104c2902c2100c190bc110241f004170b40f00000980a08806078020c8160b8120a80e0980a08806078020c8160b8120a80e000009c0d09c0d09c0d03427034270342703427034270342709c0d09c0d09c0d00000a0100b0140c01807004080080900c0a0100b0140c01807004080080900c00000a4130c41b014230ac150cc1d01c2503c2d05c0107c090442f064030840b00000a816008220382e01826048320780a0a816008220382e01826048320780a00000ac1901c2905c05054030941300423044330840f0c41f0bc1d02c2d06c0900000b01c03030080100901401028060080b01c030300801009014010280600800000b41f044030a41b0cc2505c090bc2104c050ac1d03c010640b0c4230540700000b8220580a0c826038020a81e048060b8220580a0c826038020a81e0480600000bc2506c1101c3107413024330a41f0540b0042b0841700c2d08c1903c0500000c02808018040080b02407014030040c02808018040080b024070140300400000c42b0941f0641301c010bc2908c1d05c1102c050cc2d0841b0540f0240300000c82e0a8260881e058120380a018020c82e0a8260881e058120380a0180200000cc310bc2d0ac29094230841f0741b06417054130440f02c0901c0500c010000000000000000000000000000000000000000000000000000000000000000

/-- `V x`, read in the table. -/
def look (x : Nat) : Nat := Nat.mod (Nat.shiftRight table (Nat.mul 256 x)) 115792089237316195423570985008687907853269984665640564039457584007913129639936

theorem look_eq : ∀ x : Fin 52, look x.val = V x.val := by decide +kernel

/-- `chk n lo s acc A T`: every nondecreasing list of `n` residues from `lo` on, with sum `s` and packed sums `T - acc`,
has, together with `A`, an even number of residues of the chosen order. The bounds of the loop leave only the first
elements that can be completed. -/
def chk : Nat → Nat → Nat → Nat → List Nat → Nat → Bool
  | 0, _, _, acc, A, T => cond (Nat.beq acc T) (Nat.beq (Nat.mod (nu A) 2) 0) true
  | n + 1, lo, s, acc, A, T =>
    let b := Nat.sub s (Nat.mul 51 n)
    let a := cond (Nat.ble lo b) b lo
    forallFrom a (Nat.sub (Nat.succ (Nat.div s (Nat.succ n))) a) (fun x =>
      chk n x (Nat.sub s x) (Nat.add acc (look x)) (x :: A) T)

theorem chk_sound (n : Nat) : ∀ (lo s acc T : Nat) (A L : List Nat), chk n lo s acc A T = true → L.length = n →
    L.Pairwise (· ≤ ·) → (∀ x ∈ L, lo ≤ x ∧ x ≤ 51) → L.sum = s → acc + pk (stv L) = T →
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
      have h' : forallFrom (cond (Nat.ble lo (s - 51 * n)) (s - 51 * n) lo)
          (s / (n + 1) + 1 - cond (Nat.ble lo (s - 51 * n)) (s - 51 * n) lo)
          (fun x => chk n x (s - x) (acc + look x) (x :: A) T) = true := h
      have ha : cond (Nat.ble lo (s - 51 * n)) (s - 51 * n) lo ≤ x := by
        cases hc : Nat.ble lo (s - 51 * n)
        · exact hx.1
        · show s - 51 * n ≤ x
          omega
      have hin := forallFrom_sound h' x ha (by omega)
      rw [pk_stv_cons, ← look_eq ⟨x, by omega⟩] at hT
      have := ih x (s - x) (acc + look x) T (x :: A) L' hin hl' (List.pairwise_cons.mp hp).2
        (fun y hy => ⟨hpx y hy, (hr y (List.mem_cons_of_mem _ hy)).2⟩) (by omega)
        (by rw [Nat.add_assoc]; exact hT)
      rw [List.reverse_cons, List.append_assoc]
      exact this

theorem chk0 : chk 0 1 0 0 [] 0 = true := by decide +kernel
theorem chk1 : chk 1 1 26 0 [] 44905203992412504955196221915264791213601741269566073226942093092481050 = true := by decide +kernel
theorem chk2 : chk 2 1 52 0 [] 89810407984825009910392443830529582427203482539132146453884186184962100 = true := by decide +kernel
theorem chk3 : chk 3 1 78 0 [] 134715611977237514865588665745794373640805223808698219680826279277443150 = true := by decide +kernel
theorem chk4 : chk 4 1 104 0 [] 179620815969650019820784887661059164854406965078264292907768372369924200 = true := by decide +kernel
theorem chk5 : chk 5 1 130 0 [] 224526019962062524775981109576323956068008706347830366134710465462405250 = true := by decide +kernel

theorem chk6_1 : chk 5 1 155 88079908169341784943900004715251267079110549603831698951600480717900801 [1] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_2 : chk 5 2 154 86349408353858559977407565599972951798583458096503514783625638529996802 [2] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_3 : chk 5 3 153 84618908538375335010915200774122926907804201418151786732308712819532803 [3] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_4 : chk 5 4 152 82888408722892110122320798928581737167533511494540036795799530228428804 [4] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_5 : chk 5 5 151 81157908907408964845596484912072326200885851664259588106583788091358213 [5] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_6 : chk 5 6 150 79427409092007342201664146863603896892774274788347003313116178565580806 [6] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_7 : chk 5 7 149 77696909276524117313069745018133554937113143888596399193145657493836807 [7] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_8 : chk 5 8 148 75966409544601670648044800303514690353550968549531812248208867047006216 [8] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_9 : chk 5 9 147 74235909729118445681552435405116464835293613664882528661091081975262217 [9] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_10 : chk 5 10 146 72505409913635300404904119473748191768036623791169304097549460644591626 [10] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_11 : chk 5 11 145 70774995664389056218947985818343377820515337981261611735305426138334219 [11] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_12 : chk 5 12 144 69044495848987433575015573553065706534743583506531272177519421015756812 [12] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_13 : chk 5 13 143 67313996033504208608599132595406089153543466102224617335692944370342925 [13] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_14 : chk 5 14 142 65583496218020983719928806881674491903693636904567794189693312714188814 [14] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_15 : chk 5 15 141 63852996486098616744671987193276331006532795036253387187714762956911631 [15] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_16 : chk 5 16 140 62122496670615391778255546163210001410005932509353572961952703094767632 [16] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_17 : chk 5 17 139 60391996855132166811763181264811775891748577624704289374834918023023633 [17] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_18 : chk 5 18 138 58749116866398783824985476055569480157146777309744312513198257044719634 [18] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_19 : chk 5 19 137 57018617050915638548337160051723854247021248253594678230394437872129043 [19] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_20 : chk 5 20 136 55288117235432413581844795225802981571632432551381804362538850642305044 [20] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_21 : chk 5 21 135 53557702986186169395888587353588925646450969142656357235976420539247637 [21] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_22 : chk 5 22 134 51827203170702944429472220540331838027584284214574297774532756273903638 [22] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_23 : chk 5 23 133 50096703438780497764447275825783821228631667899370856646134627346433047 [23] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_24 : chk 5 24 132 48366203623378954810282988586656005844651687871529551214768201394049048 [24] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_25 : chk 5 25 131 46635703807895729921688661030543106494128832776894257394916935280385049 [25] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel
theorem chk6_26 : chk 5 26 130 44905203992412504955196221915264791213601741269566073226942093092481050 [26] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by decide +kernel

theorem chk6 : chk 6 1 156 0 [] 269431223954475029731177331491588747281610447617396439361652558554886300 = true := by
  show forallFrom 1 26 (fun x => chk 5 x (Nat.sub 156 x) (Nat.add 0 (look x)) [x] 269431223954475029731177331491588747281610447617396439361652558554886300) = true
  simp only [forallFrom, Bool.and_eq_true]
  exact ⟨chk6_1, chk6_2, chk6_3, chk6_4, chk6_5, chk6_6, chk6_7, chk6_8, chk6_9, chk6_10, chk6_11, chk6_12, chk6_13, chk6_14, chk6_15, chk6_16, chk6_17, chk6_18, chk6_19, chk6_20, chk6_21, chk6_22, chk6_23, chk6_24, chk6_25, chk6_26, trivial⟩

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

theorem nu_perm {L₁ L₂ : List Nat} (h : L₁.Perm L₂) : nu L₁ = nu L₂ := map_sum_perm oL h

theorem short_balanced {L : List Nat} (hr : inRange L) (hl : L.length ≤ 6) (he : balanced L = true) : nu L % 2 = 0 := by
  let le : Nat → Nat → Bool := fun a b => decide (a ≤ b)
  let L' := L.mergeSort le
  have hperm : L'.Perm L := List.mergeSort_perm L le
  have hsort : L'.Pairwise (fun a b => le a b = true) :=
    List.pairwise_mergeSort (le := le) (by intro a b c h1 h2; simp [le] at *; omega)
      (by intro a b; simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) L
  have hsort' : L'.Pairwise (· ≤ ·) := hsort.imp (by intro a b h; simpa [le] using h)
  have hr' : ∀ x ∈ L', 1 ≤ x ∧ x ≤ 51 := fun x hx => hr x (hperm.mem_iff.mp hx)
  have he' : balanced L' = true := by rw [balanced_perm hperm]; exact he
  have hl' : L'.length = L.length := hperm.length_eq
  have hsum : L'.sum = 26 * L'.length := by
    have := (balanced_spec.mp he') 1 (by decide)
    rw [St_one hr'] at this
    exact this
  have hT : 0 + pk (stv L') = 26 * L'.length * R := by
    rw [Nat.zero_add]
    unfold stv
    rw [List.map_congr_left (fun t ht => (balanced_spec.mp he') t ht), pk_const]
    rfl
  have key : ∀ n, n ≤ 6 → chk n 1 (26 * n) 0 [] (26 * n * R) = true := by
    have hR : R = 1727123230477404036738316227510184277446220818060233585651618965095425 := by decide +kernel
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
  have hp := chk_sound L'.length 1 (26 * L'.length) 0 (26 * L'.length * R) [] L' (key _ (by omega)) rfl hsort' hr'
    hsum hT
  rw [List.append_nil] at hp
  rw [← nu_perm ((List.reverse_perm L').trans hperm)]
  exact hp

end FermatLength.List52
