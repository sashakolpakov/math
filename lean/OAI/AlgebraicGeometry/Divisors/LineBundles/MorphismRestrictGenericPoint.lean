import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantReferencePullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.FiberPushforward

/-! # Morphism Restrict Generic Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.MorphismRestrictGenericPoint.BundleCycles

noncomputable section

/-! # LineBundleCycles: dominance and actual generic residue degree survive restriction to a nonempty open -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
    (U : Y.Opens)
    [IsIntegral U.toScheme] [IsIntegral (f ⁻¹ᵁ U).toScheme]

include hη in
theorem morphismRestrict_genericPoint :
    (f ∣_ U) (genericPoint (f ⁻¹ᵁ U).toScheme) = genericPoint U.toScheme := by
  apply U.ι.isOpenEmbedding.injective
  have h := congrArg (fun q => q (genericPoint (f ⁻¹ᵁ U).toScheme)) (morphismRestrict_ι f U)
  change U.ι ((f ∣_ U) (genericPoint (f ⁻¹ᵁ U).toScheme)) =
    f ((f ⁻¹ᵁ U).ι (genericPoint (f ⁻¹ᵁ U).toScheme)) at h
  exact h.trans ((congrArg f (genericPoint_eq_of_isOpenImmersion (f ⁻¹ᵁ U).ι)).trans
    (hη.trans (genericPoint_eq_of_isOpenImmersion U.ι).symm))

omit [IsIntegral Y] [IsIntegral U.toScheme] in
theorem morphismRestrict_genericResidueDegree :
    (f ∣_ U).residueDegree (genericPoint (f ⁻¹ᵁ U).toScheme) = f.residueDegree (genericPoint X) := by
  have h := Open.FiberPushforward.BundleCycles.openSquare_residueDegree f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U)
    (morphismRestrict_ι f U).symm (genericPoint (f ⁻¹ᵁ U).toScheme)
  rw [genericPoint_eq_of_isOpenImmersion (f ⁻¹ᵁ U).ι] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.MorphismRestrictGenericPoint.BundleCycles
