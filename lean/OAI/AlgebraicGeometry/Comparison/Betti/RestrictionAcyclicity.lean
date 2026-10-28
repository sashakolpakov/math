import Mathlib.Algebra.Homology.Embedding.TruncGEHomology

/-! # Restriction Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.RestrictionAcyclicity.Ext

noncomputable section

/-! Restriction preserves and detects acyclicity when the original complex has the specified support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncGE] [K.IsStrictlySupported e]

def supportedRestrictionTruncIso : K.restriction e ≅ K.truncGE' e := by
  have : IsIso (K.restrictionToTruncGE' e) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact asIso (K.restrictionToTruncGE' e)

theorem supportedRestriction_acyclic (hK : K.Acyclic) : (K.restriction e).Acyclic := by
  intro i
  have h : (K.truncGE' e).ExactAt i :=
    ((K.truncGE' e).extend_exactAt_iff e rfl).mp (hK.truncGE e (e.f i))
  exact h.of_iso (supportedRestrictionTruncIso K e).symm

theorem acyclic_of_supportedRestriction (hK : (K.restriction e).Acyclic) : K.Acyclic := by
  have ht (i : ι) : (K.truncGE' e).ExactAt i :=
    (hK i).of_iso (supportedRestrictionTruncIso K e)
  have he : (K.truncGE e).Acyclic := by
    intro i'
    by_cases h : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := h
      exact ((K.truncGE' e).extend_exactAt_iff e rfl).mpr (ht i)
    · exact (K.truncGE e).exactAt_of_isSupported e i' (by simpa using h)
  intro i'
  exact (he i').of_iso (asIso (K.πTruncGE e)).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.RestrictionAcyclicity.Ext
