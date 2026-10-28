import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProjectiveMoving

/-! # Normal Principal Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.NormalPrincipalChow.Cycles

noncomputable section

/-! # LineBundleCycles: line-bundle intersection kills every actual principal divisor on a normal scheme affine over a projective scheme -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    {fY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Y fY) (q : X ⟶ Y) [IsAffineHom q]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d : ℕ)
    (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 2)

include P q hNormal hX in
theorem normalLineBundlePointIntersection_principal_zero (g : X.functionFieldˣ) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g.val)) = 0 := by
  let : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := hNormal
  obtain ⟨a, ha⟩ := L.exists_rationalSection_avoiding_principalDivisor P q g.val
  exact ProperResidueChow.Cycles.lineBundlePointIntersection_principal_zero_of_proper L a g ha hNormal f d hX

include P q hNormal hX in
theorem normalLineBundlePointIntersection_principal_nonzero (g : X.functionField) (hg : g ≠ 0) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g)) = 0 :=
  normalLineBundlePointIntersection_principal_zero P q L hNormal f d hX (Units.mk0 g hg)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.NormalPrincipalChow.Cycles
