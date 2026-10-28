import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.CurveChowDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Degree

/-! # Chow Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ChowDegree.BundleCycles

noncomputable section

/-! The projective-line infinity ideal has degree minus one on
every genuine Chow class over an arbitrary Noetherian affine base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsNoetherianRing R]
    (f : Spec (.of R) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem symmetricProjectiveLineChow_infinity_degree (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) f d
      (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R R)
        (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R) ≫ f) d
        (Degree.BundleCycles.symmetricProjectiveLineChowExtension R f d α)) = -α := by
  let : Smooth (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) :=
    (Has.BundleCycles.symmetricProjectiveLine_hasSourceCharts R).forget.smooth
  let : IsIso (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R R ≫ Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) := by
    have h : SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R R ≫ Scheme.BundleCycles.symmetricProjectiveToBase R (R × R) =
        Scheme.BundleCycles.symmetricProjectiveToBase R R :=
      Base.BundleCycles.symmetricProjectiveMap_over (LinearMap.snd R R R) (fun r => ⟨(0, r), rfl⟩)
    rw [h]
    infer_instance
  exact Cartier.CurveChowDegree.BundleCycles.cartierCurveChow_pullback_degree (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R))
    (Has.BundleCycles.symmetricProjectiveLine_hasSourceCharts R) (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R R)
    (SymmetricInfinity.Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals R R) f d α

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ChowDegree.BundleCycles
