import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AnalyticRetraction
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.Differential
import OAI.AlgebraicGeometry.CycleClass.Thom.SplitSubmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup

/-! # Retraction Equations -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.RetractionEquations.Constructions

noncomputable section

/-! Concatenating the actual ambient normal coordinates with a
submersion on the embedded source gives actual holomorphic submersion
equations in a normal neighborhood. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.Differential.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (x : Z.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x)

local instance : ChartedSpace V.analyticModel P.neighborhood :=
  inferInstanceAs (ChartedSpace V.analyticModel P.openNeighborhood)

theorem sourceInclusion_analytic :
    ContMDiff 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, V.analyticModel) ω
      (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.closed.isEmbedding) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff P.openNeighborhood (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.closed.isEmbedding) ω).mp
  exact Z.holomorphic.comp (show ContMDiff 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Z.regularAnalyticModel) ω
    (Subtype.val : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding → Z.regularAnalyticSpace) from
      contMDiff_subtype_val)

variable
  (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
    𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)))
  (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) ω
    P.ambientChart P.ambientChart.source)
  (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) 𝓘(ℂ, V.analyticModel) ω
    P.ambientChart.symm P.ambientChart.target)
  {q : ℕ}
  (g : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) ⟶ TopCat.of (Fin q → ℂ))
  (hg : ContMDiff 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Fin q → ℂ) ω g)
  (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ))

include hq hqi hg

theorem equations_analytic :
    ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin (p + q) → ℂ) ω
      (IntersectionCup.Constructions.internalNormalMap P.normalCoordinate (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding ≫ g) e) := by
  have hr := NormalPair.AnalyticRetraction.Constructions.retraction_analytic (Q := P) (hf := Z.closed.isEmbedding)
    Z.regularComplement_isImmersionAt hq hqi
  have hp : ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, (Fin p → ℂ) × (Fin q → ℂ)) ω
      (fun y => (P.normalCoordinate y, g (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding y))) :=
    (contMDiff_prod_module_iff _).mpr ⟨NormalPair.Differential.Constructions.normalCoordinate_analytic P hq, hg.comp hr⟩
  exact e.toContinuousLinearMap.contDiff.contMDiff.comp hp

include hP in
theorem equations_submersion (y : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)
    (hgs : Function.Surjective (mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Fin q → ℂ) g y)) :
    Function.Surjective (mfderiv 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin (p + q) → ℂ)
      (IntersectionCup.Constructions.internalNormalMap P.normalCoordinate (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding ≫ g) e)
      (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.closed.isEmbedding y)) := by
  let i := HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.closed.isEmbedding
  let r := HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding
  let h := r ≫ g
  have hn := NormalPair.Differential.Constructions.normalCoordinate_analytic P hq
  have hr := NormalPair.AnalyticRetraction.Constructions.retraction_analytic (Q := P) (hf := Z.closed.isEmbedding)
    Z.regularComplement_isImmersionAt hq hqi
  have hh : ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin q → ℂ) ω h := hg.comp hr
  have hzero : P.normalCoordinate ∘ i = fun _ => 0 := by
    funext z
    exact (P.mem_range_iff (i z)).mp ⟨z.val, rfl⟩
  have hcomp : h ∘ i = g := by
    funext z
    change g (r (i z)) = g z
    exact congrArg g (ConcreteCategory.congr_hom (HodgeConjecture.DegreeTwo.NormalPairSourceRetraction.Constructions.normalPairSourceInclusion_retraction P Z.closed.isEmbedding) z)
  have hhs : Function.Surjective
      (mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Fin q → ℂ) (h ∘ i) y) := by
    have he := congrArg (fun k : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding → (Fin q → ℂ) =>
      (show Z.regularAnalyticModel →L[ℂ] (Fin q → ℂ) from
        mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Fin q → ℂ) k y)) hcomp
    exact (congrArg (fun L : Z.regularAnalyticModel →L[ℂ] (Fin q → ℂ) => Function.Surjective L) he).mpr hgs
  have hs := SplitSubmersion.Constructions.mfderiv_pair_surjective i P.normalCoordinate h y
    ((sourceInclusion_analytic Z x P y).mdifferentiableAt (by simp))
    ((hn (i y)).mdifferentiableAt (by simp)) ((hh (i y)).mdifferentiableAt (by simp))
    hzero (NormalPair.Differential.Constructions.normalCoordinate_submersion P hP (i y)) hhs
  have hp : MDifferentiableAt 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, (Fin p → ℂ) × (Fin q → ℂ))
      (fun z => (P.normalCoordinate z, h z)) (i y) :=
    (mdifferentiableAt_prod_module_iff _).mpr
      ⟨(hn (i y)).mdifferentiableAt (by simp), (hh (i y)).mdifferentiableAt (by simp)⟩
  have he := (e.toContinuousLinearMap.hasMFDerivAt.comp (i y) hp.hasMFDerivAt).mfderiv
  change mfderiv 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin (p + q) → ℂ)
      (IntersectionCup.Constructions.internalNormalMap P.normalCoordinate h e) (i y) =
    e.toContinuousLinearMap.comp (mfderiv 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, (Fin p → ℂ) × (Fin q → ℂ)) (fun z => (P.normalCoordinate z, h z)) (i y)) at he
  rw [he]
  exact e.surjective.comp hs

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.RetractionEquations.Constructions
