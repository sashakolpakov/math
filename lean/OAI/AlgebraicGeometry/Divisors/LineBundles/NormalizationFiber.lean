import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationStalkMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ResidueDegree

/-! # Normalization Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationFiber.BundleCycles

noncomputable section

/-! The normalized-stalk spectrum covers the entire normalization fiber
over the chosen original point, and its map is injective. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

universe u

variable (X : Scheme.{u}) [IsIntegral X]
  (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (x : U)

theorem normalizationStalkMap_residueDegree
    (y : Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField))) :
    (NormalizationStalkMap.BundleCycles.normalizationStalkMap X U hU x).residueDegree y = 1 := by
  let := NormalizationStalkMap.BundleCycles.normalizationStalkMap_stalkMap_isIso X U hU x y
  exact IntersectionTheory.ProjectionFormula.Stalk.ResidueDegree.residueDegree_of_isIso_stalkMap _ _

theorem normalizationStalkMap_covers_fiber (y : IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X)
    (hy : IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X y = x) : y ∈ Set.range (NormalizationStalkMap.BundleCycles.normalizationStalkMap X U hU x) := by
  let B := integralClosure Γ(X, U) X.functionField
  let D := integralClosure (X.presheaf.stalk x) X.functionField
  let := (Integral.ClosureLocalization.BundleCycles.normalizationStalkInclusion X U x).toRingHom.toAlgebra
  let M := Algebra.algebraMapSubmonoid B (hU.primeIdealOf x).asIdeal.primeCompl
  let : IsLocalization M D := Integral.ClosureLocalization.BundleCycles.normalizationStalk_isLocalization X U hU x
  have hyU : y ∈ IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ⁻¹ᵁ U := by
    change IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X y ∈ U
    rw [hy]
    exact x.property
  change y ∈ (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ⁻¹ᵁ U : Set (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X)) at hyU
  rw [← NormalizationCharts.BundleCycles.normalizationChartMap_range X U hU] at hyU
  obtain ⟨q, hq⟩ := hyU
  have hp : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B))) q = hU.primeIdealOf x := by
    apply hU.fromSpec.isOpenEmbedding.injective
    have hc := congrArg (fun i : Spec (.of B) ⟶ X => i q)
      (NormalizationCharts.BundleCycles.normalizationChartMap_comp X U hU)
    change IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X (NormalizationCharts.BundleCycles.normalizationChartMap X U hU q) =
      hU.fromSpec ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B))) q) at hc
    rw [← hc, hq, hy, hU.fromSpec_primeIdealOf]
  have hdisj : Disjoint (M : Set B) (q.asIdeal : Set B) := by
    rw [Set.disjoint_left]
    intro z hzM hzq
    obtain ⟨a, ha, rfl⟩ := hzM
    apply ha
    have he := congrArg PrimeSpectrum.asIdeal hp
    change Ideal.comap (algebraMap Γ(X, U) B) q.asIdeal = (hU.primeIdealOf x).asIdeal at he
    rw [← he]
    exact hzq
  have hqrange : q ∈ Set.range (PrimeSpectrum.comap (algebraMap B D)) := by
    rw [PrimeSpectrum.localization_comap_range D M]
    exact hdisj
  obtain ⟨z, hz⟩ := hqrange
  refine ⟨z, ?_⟩
  change NormalizationCharts.BundleCycles.normalizationChartMap X U hU ((Spec.map (CommRingCat.ofHom (algebraMap B D))) z) = y
  exact (congrArg (NormalizationCharts.BundleCycles.normalizationChartMap X U hU) hz).trans hq

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationFiber.BundleCycles
