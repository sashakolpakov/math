import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityProper
import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityBoundary
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian

/-! # Compactification Noetherian -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.CompactificationNoetherian.BundleCycles

section

/-! The actual projective compactification, infinity hyperplane and
affine conormal open inherit the required Noetherian and separated properties. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData)

instance globalConormalProjective_isNoetherian : AlgebraicGeometry.IsNoetherian (ProjectiveGluing.BundleCycles.globalConormalProjective I) := by
  let : IsLocallyNoetherian (ProjectiveGluing.BundleCycles.globalConormalProjective I) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveGluing.BundleCycles.globalConormalProjectiveToBase I)
  let : CompactSpace (ProjectiveGluing.BundleCycles.globalConormalProjective I) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveGluing.BundleCycles.globalConormalProjectiveToBase I)
  exact ⟨⟩

instance globalConormalInfinity_isNoetherian : AlgebraicGeometry.IsNoetherian (InfinityGluing.BundleCycles.globalConormalInfinity I) := by
  let : IsLocallyNoetherian (InfinityGluing.BundleCycles.globalConormalInfinity I) :=
    LocallyOfFiniteType.isLocallyNoetherian (InfinityGluing.BundleCycles.globalConormalInfinityToBase I)
  let : CompactSpace (InfinityGluing.BundleCycles.globalConormalInfinity I) :=
    QuasiCompact.compactSpace_of_compactSpace (InfinityGluing.BundleCycles.globalConormalInfinityToBase I)
  exact ⟨⟩

instance globalConormalSpectrum_isNoetherian : AlgebraicGeometry.IsNoetherian (DiagramGluing.BundleCycles.globalConormalSpectrum I) :=
  Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian (GlobalConormal.Compactification.BundleCycles.globalConormalCompactification I)

variable [X.IsSeparated]

instance globalConormalProjective_isSeparated : (ProjectiveGluing.BundleCycles.globalConormalProjective I).IsSeparated := ⟨by
  rw [← Limits.terminal.comp_from (ProjectiveGluing.BundleCycles.globalConormalProjectiveToBase I)]
  infer_instance⟩

instance globalConormalInfinity_isSeparated : (InfinityGluing.BundleCycles.globalConormalInfinity I).IsSeparated := ⟨by
  rw [← Limits.terminal.comp_from (InfinityGluing.BundleCycles.globalConormalInfinityToBase I)]
  infer_instance⟩

instance globalConormalSpectrum_isSeparated : (DiagramGluing.BundleCycles.globalConormalSpectrum I).IsSeparated := ⟨by
  rw [← Limits.terminal.comp_from (GlobalConormal.Compactification.BundleCycles.globalConormalCompactification I)]
  infer_instance⟩

end

/-! Proper base changes of a Noetherian separated base are
Noetherian separated schemes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y]
    (p : E ⟶ X) [IsProper p] (b : Y ⟶ X)

instance properBaseChange_isNoetherian : AlgebraicGeometry.IsNoetherian (pullback p b) := by
  let : IsLocallyNoetherian (pullback p b) := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p b)
  let : CompactSpace (pullback p b : Scheme) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd p b)
  exact ⟨⟩

instance properBaseChange_isSeparated [Y.IsSeparated] : (pullback p b).IsSeparated := ⟨by
  rw [← terminal.comp_from (pullback.snd p b)]
  infer_instance⟩

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.CompactificationNoetherian.BundleCycles
