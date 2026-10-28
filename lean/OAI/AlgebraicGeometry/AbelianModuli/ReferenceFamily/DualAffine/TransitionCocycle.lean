import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AffineDerivationPresheaf

/-! # Transition Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.TransitionCocycle

noncomputable section

/-! The transitions on the actual pairwise affine intersections form
a cocycle for the constructed derivation presheaf: the three pair terms
are restricted to the actual triple intersection before adding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] Dual.CommonOpenCocycle.dualFamilyPairAffineOpen Dual.CommonOpenCocycle.dualFamilyTripleAffineOpen

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom]
    (U : X.left.AffineOpenCover)

theorem dualCommonOpenDerivation_self (V : X.left.affineOpens) (i : U.I₀)
    (hi : V.1 ≤ (U.f i).opensRange) : Dual.CommonOpenDerivation.dualCommonOpenDerivation k X U V i i hi hi = 0 := by
  apply (Dual.CommonOpenCocycle.dualCommonOpenDerivation_eq_zero_iff k X U V i i hi hi).mpr
  apply Iso.ext
  exact (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V.1 hi).iso.inv_hom_id

theorem dualCommonOpenDerivation_antisymm (V : X.left.affineOpens) (i j : U.I₀)
    (hi : V.1 ≤ (U.f i).opensRange) (hj : V.1 ≤ (U.f j).opensRange) :
    Dual.CommonOpenDerivation.dualCommonOpenDerivation k X U V j i hj hi = -Dual.CommonOpenDerivation.dualCommonOpenDerivation k X U V i j hi hj := by
  have h := Dual.CommonOpenCocycle.dualCommonOpenDerivation_cocycle k X U V i j i hi hj hi
  rw [dualCommonOpenDerivation_self] at h
  exact eq_neg_of_add_eq_zero_right h

variable [IsSeparated X.hom]

theorem dualFamilyPairTransition_restricted_cocycle (i j l : U.I₀) :
    Dual.CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X
        (show (Dual.CommonOpenCocycle.dualFamilyTripleAffineOpen k X U i j l).1 ≤ (Dual.CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j).1 from
          inf_le_left)
        (Dual.CommonOpenCocycle.dualFamilyPairTransitionDerivation k X U i j) +
      Dual.CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X
        (show (Dual.CommonOpenCocycle.dualFamilyTripleAffineOpen k X U i j l).1 ≤ (Dual.CommonOpenCocycle.dualFamilyPairAffineOpen k X U j l).1 from
          le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (Dual.CommonOpenCocycle.dualFamilyPairTransitionDerivation k X U j l) =
      Dual.CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X
        (show (Dual.CommonOpenCocycle.dualFamilyTripleAffineOpen k X U i j l).1 ≤ (Dual.CommonOpenCocycle.dualFamilyPairAffineOpen k X U i l).1 from
          le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (Dual.CommonOpenCocycle.dualFamilyPairTransitionDerivation k X U i l) := by
  unfold Dual.CommonOpenCocycle.dualFamilyPairTransitionDerivation
  rw [Dual.CommonOpenDerivationExtension.dualCommonOpenDerivation_restrict, Dual.CommonOpenDerivationExtension.dualCommonOpenDerivation_restrict,
    Dual.CommonOpenDerivationExtension.dualCommonOpenDerivation_restrict]
  exact Dual.CommonOpenCocycle.dualFamilyTripleTransition_cocycle k X U i j l

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.TransitionCocycle
