import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityBundle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinitySupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectiveProper
import OAI.AlgebraicGeometry.Divisors.LineBundles.PullbackRange

/-! # Infinity Boundary -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityBoundary.BundleCycles

noncomputable section

/-! The actual global infinity hyperplane is exactly the complement
of the conormal affine open and lies over the same closed center. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem globalConormalInfinityInclusion_toSupport :
    InfinityInclusion.BundleCycles.globalConormalInfinityInclusion I ≫ Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport I =
      Conormal.InfinitySupport.BundleCycles.globalConormalInfinityToSupport I := by
  apply (cancel_mono I.subschemeι).mp
  rw [Category.assoc, Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport_toBase, Conormal.InfinitySupport.BundleCycles.globalConormalInfinityToSupport_toBase]
  exact InfinityInclusion.BundleCycles.globalConormalInfinityInclusion_toBase I

theorem globalConormalInfinityInclusion_range :
    Set.range (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion I) =
      (↑(Compactification.BundleCycles.globalConormalCompactification I).opensRange : Set (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjective I))ᶜ := by
  ext z
  obtain ⟨U, y, rfl⟩ := (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).exists_eq z
  have hi : (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U y ∈ Set.range (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion I) ↔
      y ∈ Set.range (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent) :=
    Set.ext_iff.mp (PullbackRange.BundleCycles.range_of_isPullback (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion_chart_isPullback I U)).symm y
  have ha : (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U y ∈ Set.range (Compactification.BundleCycles.globalConormalCompactification I) ↔
      y ∈ Set.range (Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent) :=
    Set.ext_iff.mp (PullbackRange.BundleCycles.range_of_isPullback (Compactification.BundleCycles.globalConormalCompactification_chart_isPullback I U)).symm y
  change (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U y ∈ Set.range (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion I) ↔
    (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U y ∉ Set.range (Compactification.BundleCycles.globalConormalCompactification I)
  rw [hi, ha]
  exact Set.ext_iff.mp (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion_range
    (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent) y

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityBoundary.BundleCycles
