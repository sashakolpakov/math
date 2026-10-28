import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.GlobalGluing

/-! # One Cocycle Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.OneCocycleValues

noncomputable section

/-! The literal degree-one Cech differential vanishes when its
restricted transition sections satisfy their actual cocycle equation. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat} {I : Type} (U : I → Opens X) (F : X.Presheaf AddCommGrpCat)

theorem abelianCechDelta_one (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U 1) (a : Fin 3 → I) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U 1 k a =
      F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (0 : Fin 3).succAbove)).op (k (a ∘ (0 : Fin 3).succAbove)) -
        F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (1 : Fin 3).succAbove)).op (k (a ∘ (1 : Fin 3).succAbove)) +
          F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (2 : Fin 3).succAbove)).op (k (a ∘ (2 : Fin 3).succAbove)) := by
  unfold DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta
  erw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    show (-1 : ℤ) ^ (2 : Fin 3).val = 1 by decide,
    one_zsmul, neg_one_zsmul, ← sub_eq_add_neg]

theorem abelianCech_one_closed_of_transition (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U 1)
    (h : ∀ a : Fin 3 → I,
      F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (0 : Fin 3).succAbove)).op (k (a ∘ (0 : Fin 3).succAbove)) +
        F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (2 : Fin 3).succAbove)).op (k (a ∘ (2 : Fin 3).succAbove)) =
          F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (1 : Fin 3).succAbove)).op (k (a ∘ (1 : Fin 3).succAbove))) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U 1 k = 0 := by
  funext a
  change DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U 1 k a = 0
  rw [abelianCechDelta_one]
  have he := h a
  rw [← he]
  abel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.OneCocycleValues
