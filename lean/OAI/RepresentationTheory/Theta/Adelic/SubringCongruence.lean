import Mathlib

/-! # Subring Congruence -/

namespace OAI.RepresentationTheory.Theta.Adelic.SubringCongruence

noncomputable section

/-! The image of a principal special-linear congruence group in an
ambient ring is exactly the stated entrywise ideal congruence. -/

open scoped Classical _root_.Matrix

variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]

def congruenceImage (S : Subring R) (I : Ideal S) :
    Subgroup (Matrix.SpecialLinearGroup J R) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk I)).ker.map
    (Matrix.SpecialLinearGroup.map S.subtype)

omit [Fintype J] in
theorem map_one_entry {T : Type*} [CommRing T] (f : T →+* R) (i j : J) :
    f ((1 : Matrix J J T) i j) = (1 : Matrix J J R) i j := by
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem congruenceImage_mem_iff (S : Subring R) (I : Ideal S)
    (g : Matrix.SpecialLinearGroup J R) :
    g ∈ congruenceImage S I ↔
      ∀ i j, ∃ x : S, x ∈ I ∧ g.val i j - (1 : Matrix J J R) i j = (x : R) := by
  constructor
  · rintro ⟨h, hh, rfl⟩ i j
    have he := congrArg (fun a : Matrix.SpecialLinearGroup J (S ⧸ I) => a.val i j) hh
    change Ideal.Quotient.mk I (h.val i j) = (1 : Matrix J J (S ⧸ I)) i j at he
    rw [← map_one_entry (Ideal.Quotient.mk I)] at he
    refine ⟨h.val i j - (1 : Matrix J J S) i j,
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he, ?_⟩
    change (h.val i j : R) - (1 : Matrix J J R) i j =
      S.subtype (h.val i j - (1 : Matrix J J S) i j)
    rw [map_sub, map_one_entry]
    rfl
  · intro hg
    choose x hx he using hg
    let M : Matrix J J S := fun i j => x i j + (1 : Matrix J J S) i j
    have hM : M.map S.subtype = g.val := by
      ext i j
      change S.subtype (x i j + (1 : Matrix J J S) i j) = g.val i j
      rw [map_add, map_one_entry]
      exact (sub_eq_iff_eq_add.mp (he i j)).symm
    have hdet : M.det = 1 := by
      apply Subtype.val_injective
      change S.subtype M.det = S.subtype 1
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hM, g.property, map_one]
    let h : Matrix.SpecialLinearGroup J S := ⟨M, hdet⟩
    refine ⟨h, ?_, ?_⟩
    · apply Matrix.SpecialLinearGroup.ext
      intro i j
      change Ideal.Quotient.mk I (x i j + (1 : Matrix J J S) i j) =
        (1 : Matrix J J (S ⧸ I)) i j
      rw [map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr (hx i j), zero_add, map_one_entry]
    · exact Subtype.ext hM

end

end OAI.RepresentationTheory.Theta.Adelic.SubringCongruence
