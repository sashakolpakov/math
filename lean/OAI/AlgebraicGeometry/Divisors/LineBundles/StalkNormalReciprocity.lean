import OAI.AlgebraicGeometry.Divisors.LineBundles.StalkRationalOrder
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.NormalReciprocity

/-! # Stalk Normal Reciprocity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.StalkNormalReciprocity.BundleCycles

noncomputable section

/-!
# LineBundleCycles: complete reciprocity on the actual codimension-two stalk spectrum

The local surface is the scheme's actual stalk. The rational functions
are transported by its actual generic-field map.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (x : X) [IsIntegrallyClosed (X.presheaf.stalk x)]

theorem normalStalkResidueBoundary_zero (hx : coheight x = 2) (g h : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (X.presheaf.stalk x))
      (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed (X.presheaf.stalk x))
      (Units.map (StalkRationalOrder.BundleCycles.stalkFunctionFieldMap X x).hom.toMonoidHom g)
      (Units.map (StalkRationalOrder.BundleCycles.stalkFunctionFieldMap X x).hom.toMonoidHom h) = 0 := by
  have hdim : ringKrullDim (X.presheaf.stalk x) = 2 := by
    rw [ringKrullDim_stalk_eq_coheight, hx]
    rfl
  exact Affine.NormalReciprocity.BundleCycles.affineNormalResidueBoundary_zero (X.presheaf.stalk x) hdim _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.StalkNormalReciprocity.BundleCycles
