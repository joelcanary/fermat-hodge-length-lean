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

public import FermatLength.Defs

/-!
# From `R_d` to lists of residues
-/

@[expose] public section

namespace FermatLength

/-- The opposite residue. -/
def opp {d : ℕ} (a : Res d) : Res d := ⟨-a.1, neg_ne_zero.mpr a.2⟩

lemma len_single {d : ℕ} (a : Res d) (n : ℤ) : len (Finsupp.single a n) = n.natAbs := by
  simp [len, Finsupp.sum_single_index]

/-- Every element of `R_d` can be replaced by a list of residues as long as its length: a coefficient `n < 0` of
`(a)` becomes `-n` copies of `(-a)`. -/
lemma exists_list {d : ℕ} (β : R d) : ∃ l : List (Res d), l.length = len β ∧
    ∀ {A : Type} [AddCommGroup A] (ψ : R d →+ A),
      (∀ a, ψ (Finsupp.single (opp a) 1) = -ψ (Finsupp.single a 1)) → ψ (tuple l) = ψ β := by
  classical
  induction β using Finsupp.induction with
  | zero => exact ⟨[], by simp [len], by intro A _ ψ _; simp [tuple]⟩
  | single_add a n f ha hn ih =>
    obtain ⟨l, hl, h⟩ := ih
    have hlen : len (Finsupp.single a n + f) = n.natAbs + len f := by
      unfold len
      rw [Finsupp.sum_add_index_of_disjoint]
      · rw [Finsupp.sum_single_index (by simp)]
      · refine Finset.disjoint_of_subset_left Finsupp.support_single_subset ?_
        simpa using ha
    refine ⟨List.replicate n.natAbs (if 0 < n then a else opp a) ++ l, by simp [hl, hlen], ?_⟩
    intro A _ ψ hψ
    have hs : ψ (Finsupp.single a n) = n • ψ (Finsupp.single a 1) := by
      rw [← map_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
    have ht : ψ (tuple (List.replicate n.natAbs (if 0 < n then a else opp a))) =
        n • ψ (Finsupp.single a 1) := by
      simp only [tuple, List.map_replicate, List.sum_replicate, map_nsmul]
      split_ifs with h0
      · rw [← natCast_zsmul, Int.natCast_natAbs, abs_of_pos h0]
      · rw [hψ, ← natCast_zsmul, Int.natCast_natAbs, abs_of_nonpos (not_lt.mp h0), neg_smul, smul_neg,
          neg_neg]
    have hta : tuple (List.replicate n.natAbs (if 0 < n then a else opp a) ++ l) =
        tuple (List.replicate n.natAbs (if 0 < n then a else opp a)) + tuple l := by
      simp [tuple]
    rw [hta, map_add, map_add, ht, hs, h ψ hψ]

/-- The homomorphism of `R_d` with given values on the residues. -/
noncomputable def hom {d : ℕ} {A : Type} [AddCommGroup A] (f : Res d → A) : R d →+ A :=
  Finsupp.liftAddHom fun a => (zmultiplesHom A) (f a)

lemma hom_single {d : ℕ} {A : Type} [AddCommGroup A] (f : Res d → A) (a : Res d) :
    hom f (Finsupp.single a 1) = f a := by
  simp [hom]

lemma hom_tuple {d : ℕ} {A : Type} [AddCommGroup A] (f : Res d → A) (l : List (Res d)) :
    hom f (tuple l) = (l.map f).sum := by
  induction l with
  | nil => simp [tuple]
  | cons a l ih =>
    have : tuple (a :: l) = Finsupp.single a 1 + tuple l := by simp [tuple]
    rw [this, map_add, hom_single, ih, List.map_cons, List.sum_cons]

lemma len_add_le {d : ℕ} (f g : R d) : len (f + g) ≤ len f + len g := by
  classical
  have hf : len f = ∑ x ∈ f.support ∪ g.support, (f x).natAbs :=
    Finsupp.sum_of_support_subset _ Finset.subset_union_left _ (by simp)
  have hg : len g = ∑ x ∈ f.support ∪ g.support, (g x).natAbs :=
    Finsupp.sum_of_support_subset _ Finset.subset_union_right _ (by simp)
  have hfg : len (f + g) = ∑ x ∈ f.support ∪ g.support, ((f + g) x).natAbs :=
    Finsupp.sum_of_support_subset _ Finsupp.support_add _ (by simp)
  rw [hf, hg, hfg, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => Int.natAbs_add_le _ _

lemma len_tuple_le {d : ℕ} (l : List (Res d)) : len (tuple l) ≤ l.length := by
  induction l with
  | nil => simp [tuple, len]
  | cons a l ih =>
    have e : tuple (a :: l) = Finsupp.single a 1 + tuple l := by simp [tuple]
    have h := len_add_le (Finsupp.single a 1) (tuple l)
    rw [len_single] at h
    rw [e, List.length_cons]
    simp only [Int.natAbs_one] at h
    omega

/-- The exact length from a lower bound: `ξ` has `n` entries, and every `β` in its class has length at least `n`. -/
lemma lenMod_eq {d : ℕ} {G : AddSubgroup (R d)} {l : List (Res d)} {n : ℕ} (hl : l.length = n)
    (h : ∀ β : R d, tuple l - β ∈ G → n ≤ len β) : lenMod G (tuple l) = n := by
  have hmem : len (tuple l) ∈ {m | ∃ β : R d, tuple l - β ∈ G ∧ len β = m} :=
    ⟨tuple l, by simp, rfl⟩
  have h1 : lenMod G (tuple l) ≤ n := (Nat.sInf_le hmem).trans ((len_tuple_le l).trans hl.le)
  have h2 : n ≤ lenMod G (tuple l) := by
    obtain ⟨β, hβ, he⟩ := Nat.sInf_mem ⟨_, hmem⟩
    unfold lenMod
    rw [← he]
    exact h β hβ
  exact le_antisymm h1 h2

/-- A homomorphism that is zero on the generators is constant on the classes modulo `D ⊔ SAll`. -/
lemma hom_class {d : ℕ} {A : Type} [AddCommGroup A] (f : Res d → A)
    (hpair : ∀ a b : Res d, a.1 + b.1 = 0 → f a + f b = 0) (heps : ∀ e : Res d, e.1 + e.1 = 0 → f e = 0)
    (hstd : ∀ (p k : ℕ) (i : ZMod d) (l : List (Res d)), p.Prime → d = p * k → 3 ≤ k →
      l.map Subtype.val = standard d p k i → (l.map f).sum = 0)
    {α β : R d} (h : α - β ∈ D d ⊔ SAll d) : hom f α = hom f β := by
  have hle : D d ⊔ SAll d ≤ (hom f).ker := by
    refine sup_le ?_ ?_
    · refine (AddSubgroup.closure_le _).mpr ?_
      rintro r (⟨a, b, hab, rfl⟩ | ⟨e, he, rfl⟩)
      · simp [AddMonoidHom.mem_ker, hom_tuple, hpair a b hab]
      · simp [AddMonoidHom.mem_ker, hom_tuple, heps e he]
    · refine (AddSubgroup.closure_le _).mpr ?_
      rintro r ⟨p, k, i, l, hp, hd, hk, hl, rfl⟩
      simp [AddMonoidHom.mem_ker, hom_tuple, hstd p k i l hp hd hk hl]
  have := hle h
  rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero] at this
  exact this

lemma S_le_SAll (d : ℕ) : S d ≤ SAll d :=
  AddSubgroup.closure_mono fun _ ⟨p, k, i, l, hp, hd, hk, _, hl, hr⟩ => ⟨p, k, i, l, hp, hd, hk, hl, hr⟩

end FermatLength
