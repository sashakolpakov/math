import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EulerShifts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassGroup
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EulerPullbackIso

/-! # Class Euler Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassEulerIsomorphism

noncomputable section

/-! Euler characteristic of bundle classes is invariant under an actual
isomorphism over the coefficient field. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem lineBundleClassEuler_pullback_overIso
    {k : Type u} [Field k] {X Y : Over (Spec (.of k))} [Y.left.IsSeparated]
    (e : X ≅ Y) (q : Line.Bundles.LineBundle.IsoClass Y.left) :
    EulerShifts.lineBundleClassEuler X.hom (Line.Bundles.LineBundle.pullbackClass e.hom.left q) =
      EulerShifts.lineBundleClassEuler Y.hom q := by
  induction q using Quotient.inductionOn with
  | h L =>
    exact EulerPullbackIso.coefficientEulerCharacteristic_overIso e L (L.pullback e.hom.left) (Iso.refl _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassEulerIsomorphism
