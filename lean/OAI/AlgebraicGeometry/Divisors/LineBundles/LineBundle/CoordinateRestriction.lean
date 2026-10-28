import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FrameComparison
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalSection
import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalBoundary

/-! # Coordinate Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: genuine function-field coordinates of rational sections on every smaller common open -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionCoordinate_on_open (x : X) (W : X.Opens) [Nonempty W]
    (hW : W ≤ L.rationalCoordinateDomain x) :
    L.rationalSectionCoordinate x =
      Units.map (X.germToFunctionField W).hom.toMonoidHom
        (L.ambientTransitionOn x (genericPoint X) W (hW.trans inf_le_left) (hW.trans inf_le_right)) := by
  have ht := L.ambientTransitionOn_restrict x (genericPoint X) hW inf_le_left inf_le_right
  rw [← ht]
  apply Units.ext
  exact (RationalBoundary.BundleCycles.RationalUnitRepresentative.germ_restrict hW
    (L.ambientTransitionOn x (genericPoint X) (L.rationalCoordinateDomain x) inf_le_left inf_le_right :
      Γ(X, L.rationalCoordinateDomain x))).symm

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionCoordinate_reference : L.rationalSectionCoordinate (genericPoint X) = 1 := by
  unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionCoordinate
  rw [L.ambientTransitionOn_self, map_one]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
