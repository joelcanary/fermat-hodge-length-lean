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

public import FermatLength.Bridge
public import FermatLength.List52

/-!
# Degree 52

The additive functions `g t` (one for each unit `t`) and the parity `h` of the number of residues of order 13 vanish on the
generators of `D + SAll`, so they are constant on each class. On the class of `ξ` the `g t` are zero and `h` is one, and no
list of at most six residues has those values.
-/

@[expose] public section

set_option maxRecDepth 4000

namespace FermatLength

namespace Deg52

/-- The additive functions behind Shioda's condition: `2 (t a mod 52) - 52`. -/
def g (t : ℕ) (a : ZMod 52) : ℤ := 2 * ((t * a.val % 52 : ℕ) : ℤ) - 52

/-- The parity of the number of residues of order 13. -/
def h (a : ZMod 52) : ZMod 2 := ((List52.oL a.val : ℕ) : ZMod 2)

lemma g_neg : ∀ t ∈ List52.U, ∀ a : ZMod 52, a ≠ 0 → g t (-a) = -g t a := by
  decide +kernel

lemma h_neg : ∀ a : ZMod 52, h (-a) = -h a := by
  decide +kernel

lemma two_torsion : ∀ a : ZMod 52, a ≠ 0 → a + a = 0 → a = 26 := by
  decide +kernel

lemma g_eps : ∀ t ∈ List52.U, g t 26 = 0 := by
  decide +kernel

lemma h_eps : h 26 = 0 := by
  decide +kernel

lemma g_std2 : ∀ i : ZMod 52, (∀ x ∈ standard 52 2 26 i, x ≠ 0) →
    ∀ t ∈ List52.U, ((standard 52 2 26 i).map (g t)).sum = 0 := by
  decide +kernel

lemma h_std2 : ∀ i : ZMod 52, (∀ x ∈ standard 52 2 26 i, x ≠ 0) →
    ((standard 52 2 26 i).map h).sum = 0 := by
  decide +kernel

lemma g_std : ∀ i : ZMod 52, (∀ x ∈ standard 52 13 4 i, x ≠ 0) →
    ∀ t ∈ List52.U, ((standard 52 13 4 i).map (g t)).sum = 0 := by
  decide +kernel

lemma h_std : ∀ i : ZMod 52, (∀ x ∈ standard 52 13 4 i, x ≠ 0) →
    ((standard 52 13 4 i).map h).sum = 0 := by
  decide +kernel

lemma factor {p k : ℕ} (hp : p.Prime) (hd : 52 = p * k) (hk : 3 ≤ k) :
    (p = 2 ∧ k = 26) ∨ (p = 13 ∧ k = 4) := by
  have h3 : p ≤ 17 := by
    by_contra hlt
    have : (17 + 1) * 3 ≤ p * k := Nat.mul_le_mul (by omega) hk
    omega
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

/-- A function of the residues that is odd and zero on the standard tuples is constant on the classes. -/
lemma class_const {A : Type} [AddCommGroup A] (f : ZMod 52 → A)
    (hneg : ∀ a : ZMod 52, a ≠ 0 → f (-a) = -f a) (heps : f 26 = 0)
    (h2 : ∀ i : ZMod 52, (∀ x ∈ standard 52 2 26 i, x ≠ 0) → ((standard 52 2 26 i).map f).sum = 0)
    (hp : ∀ i : ZMod 52, (∀ x ∈ standard 52 13 4 i, x ≠ 0) → ((standard 52 13 4 i).map f).sum = 0)
    {α β : R 52} (hab : α - β ∈ D 52 ⊔ SAll 52) :
    hom (fun a : Res 52 => f a.1) α = hom (fun a : Res 52 => f a.1) β := by
  refine hom_class _ ?_ ?_ ?_ hab
  · intro a b e
    have hb : b.1 = -a.1 := (neg_eq_of_add_eq_zero_right e).symm
    rw [hb, hneg a.1 a.2, add_neg_cancel]
  · intro e he
    rw [two_torsion e.1 e.2 he, heps]
  · intro p k i l hprime hd hk hl
    have hmap : (l.map fun a : Res 52 => f a.1) = (standard 52 p k i).map f := by
      rw [← hl, List.map_map]
      rfl
    have hne : ∀ x ∈ standard 52 p k i, x ≠ 0 := by
      intro x hx
      rw [← hl, List.mem_map] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact a.2
    rw [hmap]
    rcases factor hprime hd hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h2 i hne
    · exact hp i hne

lemma sum_g (t : ℕ) (l : List (Res 52)) : (l.map fun a : Res 52 => g t a.1).sum =
    2 * (List52.St t (l.map fun a => a.1.val) : ℤ) - 52 * l.length := by
  induction l with
  | nil => simp [List52.St]
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List52.St, List.map_cons, List.sum_cons, List.length_cons, g]
    push_cast
    ring

lemma sum_h (l : List (Res 52)) : (l.map fun a : Res 52 => h a.1).sum =
    ((List52.nu (l.map fun a => a.1.val) : ℕ) : ZMod 2) := by
  induction l with
  | nil => simp [List52.nu]
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp [List52.nu, h]

lemma xi_g : ∀ t ∈ List52.U, (xi52.map fun a : Res 52 => g t a.1).sum = 0 := by
  decide +kernel

lemma xi_h : (xi52.map fun a : Res 52 => h a.1).sum = 1 := by
  decide +kernel

lemma lower {β : R 52} (hβ : tuple xi52 - β ∈ D 52 ⊔ SAll 52) : 7 ≤ len β := by
  obtain ⟨l, hl, hψ⟩ := exists_list β
  by_contra hlt
  have hr : List52.inRange (l.map fun a => a.1.val) := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    have h0 : a.1.val ≠ 0 := by
      rw [Ne, ZMod.val_eq_zero]
      exact a.2
    have h1 : a.1.val < 52 := ZMod.val_lt a.1
    omega
  have hb : List52.balanced (l.map fun a => a.1.val) = true := by
    rw [List52.balanced_spec]
    intro t ht
    have e1 := class_const (g t) (fun a ha => g_neg t ht a ha) (g_eps t ht) (fun i hi => g_std2 i hi t ht)
      (fun i hi => g_std i hi t ht) hβ
    have e2 := hψ (hom fun a : Res 52 => g t a.1) (fun a => by
      rw [hom_single, hom_single]
      exact g_neg t ht a.1 a.2)
    rw [← e1, hom_tuple, hom_tuple, xi_g t ht, sum_g] at e2
    rw [List.length_map]
    omega
  have hn : ((List52.nu (l.map fun a => a.1.val) : ℕ) : ZMod 2) = 1 := by
    have e1 := class_const h (fun a _ => h_neg a) h_eps h_std2 h_std hβ
    have e2 := hψ (hom fun a : Res 52 => h a.1) (fun a => by
      rw [hom_single, hom_single]
      exact h_neg a.1)
    rw [← e1, hom_tuple, hom_tuple, xi_h, sum_h] at e2
    exact e2
  have hs := List52.short_balanced hr (by rw [List.length_map]; omega) hb
  have h0 : ((List52.nu (l.map fun a => a.1.val) : ℕ) : ZMod 2) = 0 :=
    (ZMod.natCast_eq_zero_iff_even).mpr (Nat.even_iff.mpr hs)
  rw [h0] at hn
  exact absurd hn (by decide)

end Deg52

/-- **The length of `ξ` in degree 52 is exactly seven**: no element of `R_52` of length at most six differs from
`ξ` by an element of `D_52 + S_52`. -/
theorem lenMod_xi52 : lenMod (D 52 ⊔ S 52) (tuple xi52) = 7 := by
  exact lenMod_eq rfl fun _ hβ => Deg52.lower (sup_le_sup_left (S_le_SAll 52) (D 52) hβ)

/-- The same modulo the larger subgroup generated by `D_52` and all the standard tuples, without the condition
`p ∤ i`. -/
theorem lenMod_xi52_all : lenMod (D 52 ⊔ SAll 52) (tuple xi52) = 7 := by
  exact lenMod_eq rfl fun _ hβ => Deg52.lower hβ

end FermatLength
