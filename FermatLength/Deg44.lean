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
public import FermatLength.List44

/-!
# Degree 44

The additive functions `g t` (one for each unit `t`) and the parity `h` of the number of residues of order 11 vanish on the
generators of `D + SAll`, so they are constant on each class. On the class of `ξ` the `g t` are zero and `h` is one, and no
list of at most six residues has those values.
-/

@[expose] public section

set_option maxRecDepth 4000

namespace FermatLength

namespace Deg44

/-- The additive functions behind Shioda's condition: `2 (t a mod 44) - 44`. -/
def g (t : ℕ) (a : ZMod 44) : ℤ := 2 * ((t * a.val % 44 : ℕ) : ℤ) - 44

/-- The parity of the number of residues of order 11. -/
def h (a : ZMod 44) : ZMod 2 := ((List44.o11 a.val : ℕ) : ZMod 2)

lemma g_neg : ∀ t ∈ List44.U, ∀ a : ZMod 44, a ≠ 0 → g t (-a) = -g t a := by
  decide +kernel

lemma h_neg : ∀ a : ZMod 44, h (-a) = -h a := by
  decide +kernel

lemma two_torsion : ∀ a : ZMod 44, a ≠ 0 → a + a = 0 → a = 22 := by
  decide +kernel

lemma g_eps : ∀ t ∈ List44.U, g t 22 = 0 := by
  decide +kernel

lemma h_eps : h 22 = 0 := by
  decide +kernel

lemma g_std2 : ∀ i : ZMod 44, (∀ x ∈ standard 44 2 22 i, x ≠ 0) →
    ∀ t ∈ List44.U, ((standard 44 2 22 i).map (g t)).sum = 0 := by
  decide +kernel

lemma h_std2 : ∀ i : ZMod 44, (∀ x ∈ standard 44 2 22 i, x ≠ 0) →
    ((standard 44 2 22 i).map h).sum = 0 := by
  decide +kernel

lemma g_std : ∀ i : ZMod 44, (∀ x ∈ standard 44 11 4 i, x ≠ 0) →
    ∀ t ∈ List44.U, ((standard 44 11 4 i).map (g t)).sum = 0 := by
  decide +kernel

lemma h_std : ∀ i : ZMod 44, (∀ x ∈ standard 44 11 4 i, x ≠ 0) →
    ((standard 44 11 4 i).map h).sum = 0 := by
  decide +kernel

lemma factor {p k : ℕ} (hp : p.Prime) (hd : 44 = p * k) (hk : 3 ≤ k) :
    (p = 2 ∧ k = 22) ∨ (p = 11 ∧ k = 4) := by
  have h3 : p ≤ 14 := by
    by_contra hlt
    have : (14 + 1) * 3 ≤ p * k := Nat.mul_le_mul (by omega) hk
    omega
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

/-- A function of the residues that is odd and zero on the standard tuples is constant on the classes. -/
lemma class_const {A : Type} [AddCommGroup A] (f : ZMod 44 → A)
    (hneg : ∀ a : ZMod 44, a ≠ 0 → f (-a) = -f a) (heps : f 22 = 0)
    (h2 : ∀ i : ZMod 44, (∀ x ∈ standard 44 2 22 i, x ≠ 0) → ((standard 44 2 22 i).map f).sum = 0)
    (hp : ∀ i : ZMod 44, (∀ x ∈ standard 44 11 4 i, x ≠ 0) → ((standard 44 11 4 i).map f).sum = 0)
    {α β : R 44} (hab : α - β ∈ D 44 ⊔ SAll 44) :
    hom (fun a : Res 44 => f a.1) α = hom (fun a : Res 44 => f a.1) β := by
  refine hom_class _ ?_ ?_ ?_ hab
  · intro a b e
    have hb : b.1 = -a.1 := (neg_eq_of_add_eq_zero_right e).symm
    rw [hb, hneg a.1 a.2, add_neg_cancel]
  · intro e he
    rw [two_torsion e.1 e.2 he, heps]
  · intro p k i l hprime hd hk hl
    have hmap : (l.map fun a : Res 44 => f a.1) = (standard 44 p k i).map f := by
      rw [← hl, List.map_map]
      rfl
    have hne : ∀ x ∈ standard 44 p k i, x ≠ 0 := by
      intro x hx
      rw [← hl, List.mem_map] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact a.2
    rw [hmap]
    rcases factor hprime hd hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h2 i hne
    · exact hp i hne

lemma sum_g (t : ℕ) (l : List (Res 44)) : (l.map fun a : Res 44 => g t a.1).sum =
    2 * (List44.St t (l.map fun a => a.1.val) : ℤ) - 44 * l.length := by
  induction l with
  | nil => simp [List44.St]
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List44.St, List.map_cons, List.sum_cons, List.length_cons, g]
    push_cast
    ring

lemma sum_h (l : List (Res 44)) : (l.map fun a : Res 44 => h a.1).sum =
    ((List44.nu (l.map fun a => a.1.val) : ℕ) : ZMod 2) := by
  induction l with
  | nil => simp [List44.nu]
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp [List44.nu, h]

lemma xi_g : ∀ t ∈ List44.U, (xi44.map fun a : Res 44 => g t a.1).sum = 0 := by
  decide +kernel

lemma xi_h : (xi44.map fun a : Res 44 => h a.1).sum = 1 := by
  decide +kernel

lemma lower {β : R 44} (hβ : tuple xi44 - β ∈ D 44 ⊔ SAll 44) : 7 ≤ len β := by
  obtain ⟨l, hl, hψ⟩ := exists_list β
  by_contra hlt
  have hr : List44.inRange (l.map fun a => a.1.val) := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    have h0 : a.1.val ≠ 0 := by
      rw [Ne, ZMod.val_eq_zero]
      exact a.2
    have h1 : a.1.val < 44 := ZMod.val_lt a.1
    omega
  have hb : List44.balanced (l.map fun a => a.1.val) = true := by
    rw [List44.balanced_spec]
    intro t ht
    have e1 := class_const (g t) (fun a ha => g_neg t ht a ha) (g_eps t ht) (fun i hi => g_std2 i hi t ht)
      (fun i hi => g_std i hi t ht) hβ
    have e2 := hψ (hom fun a : Res 44 => g t a.1) (fun a => by
      rw [hom_single, hom_single]
      exact g_neg t ht a.1 a.2)
    rw [← e1, hom_tuple, hom_tuple, xi_g t ht, sum_g] at e2
    rw [List.length_map]
    omega
  have hn : ((List44.nu (l.map fun a => a.1.val) : ℕ) : ZMod 2) = 1 := by
    have e1 := class_const h (fun a _ => h_neg a) h_eps h_std2 h_std hβ
    have e2 := hψ (hom fun a : Res 44 => h a.1) (fun a => by
      rw [hom_single, hom_single]
      exact h_neg a.1)
    rw [← e1, hom_tuple, hom_tuple, xi_h, sum_h] at e2
    exact e2
  have hs := List44.short_balanced hr (by rw [List.length_map]; omega) hb
  have h0 : ((List44.nu (l.map fun a => a.1.val) : ℕ) : ZMod 2) = 0 :=
    (ZMod.natCast_eq_zero_iff_even).mpr (Nat.even_iff.mpr hs)
  rw [h0] at hn
  exact absurd hn (by decide)

end Deg44

/-- **The length of `ξ` in degree 44 is exactly seven**: no element of `R_44` of length at most six differs from
`ξ` by an element of `D_44 + S_44`. -/
theorem lenMod_xi44 : lenMod (D 44 ⊔ S 44) (tuple xi44) = 7 := by
  exact lenMod_eq rfl fun _ hβ => Deg44.lower (sup_le_sup_left (S_le_SAll 44) (D 44) hβ)

/-- The same modulo the larger subgroup generated by `D_44` and all the standard tuples, without the condition
`p ∤ i`. -/
theorem lenMod_xi44_all : lenMod (D 44 ⊔ SAll 44) (tuple xi44) = 7 := by
  exact lenMod_eq rfl fun _ hβ => Deg44.lower hβ

end FermatLength
