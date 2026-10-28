import OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.Differential
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition
import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceSupport

/-! # Nested Normal Equation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NestedNormalEquation.Constructions

noncomputable section

/-! Actual normal coordinates of the inner immersion restrict to
submersion equations on a sufficiently small outer normal source open.
Their zero set is the actual open restriction of the composite immersion. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions
  Closed.ImmersionOpenRestriction.Constructions Open.InclusionDifferential.Constructions NormalPair.Differential.Constructions HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.sourceManifold Z) q) (z : C.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion
    (C.regularComplementInclusion z))
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair C.regularAnalyticModel (Fin q → ℂ) C.regularComplementInclusion z)
  (hPQ : Z.regularComplementInclusion ⁻¹' P.neighborhood ⊆ Q.neighborhood)

local instance : ChartedSpace Z.regularAnalyticModel Q.neighborhood :=
  inferInstanceAs (ChartedSpace Z.regularAnalyticModel Q.openNeighborhood)

local instance : ChartedSpace Z.regularAnalyticModel (Q.openNeighborhood : Set Z.regularAnalyticSpace) :=
  inferInstanceAs (ChartedSpace Z.regularAnalyticModel Q.openNeighborhood)

local instance : ChartedSpace Z.regularAnalyticModel
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding : Set Z.regularAnalyticSpace) :=
  inferInstanceAs (ChartedSpace Z.regularAnalyticModel (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding))

def parameterInclusion : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) ⟶
    TopCat.of Q.neighborhood :=
  TopCat.ofHom ⟨fun y => ⟨y.val, hPQ y.property⟩, continuous_subtype_val.subtype_mk _⟩

def parameter : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) ⟶ TopCat.of (Fin q → ℂ) :=
  parameterInclusion Z C z P Q hPQ ≫ Q.normalCoordinate

theorem parameter_analytic
    (hQ : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, C.regularAnalyticModel × (Fin q → ℂ)) ω
      Q.ambientChart Q.ambientChart.source) :
    ContMDiff 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Fin q → ℂ) ω (parameter Z C z P Q hPQ) :=
  (NormalPair.Differential.Constructions.normalCoordinate_analytic Q hQ).comp
    (Open.InclusionDifferential.Constructions.openInclusion_analytic (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) Q.openNeighborhood hPQ)

theorem parameter_submersion
    (hQd : Q.ambientChart.MDifferentiable 𝓘(ℂ, Z.regularAnalyticModel)
      𝓘(ℂ, C.regularAnalyticModel × (Fin q → ℂ)))
    (hQ : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, C.regularAnalyticModel × (Fin q → ℂ)) ω
      Q.ambientChart Q.ambientChart.source)
    (y : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) :
    Function.Surjective (mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Fin q → ℂ)
      (parameter Z C z P Q hPQ) y) := by
  have hi := Open.InclusionDifferential.Constructions.openInclusion_analytic (E := Z.regularAnalyticModel)
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) Q.openNeighborhood hPQ
  have he := mfderiv_comp y
    (((NormalPair.Differential.Constructions.normalCoordinate_analytic Q hQ) (parameterInclusion Z C z P Q hPQ y)).mdifferentiableAt (by simp))
    ((hi y).mdifferentiableAt (by simp))
  have hd : mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Z.regularAnalyticModel)
      (parameterInclusion Z C z P Q hPQ) y = ContinuousLinearMap.id ℂ Z.regularAnalyticModel :=
    Open.InclusionDifferential.Constructions.openInclusion_mfderiv (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) Q.openNeighborhood hPQ y
  rw [hd] at he
  change mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Fin q → ℂ) (parameter Z C z P Q hPQ) y =
    (mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Fin q → ℂ) Q.normalCoordinate
      (parameterInclusion Z C z P Q hPQ y)).comp (ContinuousLinearMap.id ℂ Z.regularAnalyticModel) at he
  exact (congrArg (fun L : Z.regularAnalyticModel →L[ℂ] (Fin q → ℂ) => Function.Surjective L) he).mpr
    (NormalPair.Differential.Constructions.normalCoordinate_submersion Q hQd (parameterInclusion Z C z P Q hPQ y))

theorem parameter_zero_iff (y : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) :
    parameter Z C z P Q hPQ y = 0 ↔ y.val ∈ Set.range C.regularComplementInclusion :=
  (Q.mem_range_iff (parameterInclusion Z C z P Q hPQ y)).symm

theorem composite_restriction_range :
    Set.range (Closed.ImmersionOpenRestriction.Constructions.restrict (Open.ClosedImmersionComposition.Constructions.compose Z C) P.openNeighborhood).regularComplementInclusion =
      (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.closed.isEmbedding) '' (parameter Z C z P Q hPQ ⁻¹' {0}) := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    let t : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding := ⟨C.regularComplementInclusion w.val, w.property⟩
    exact ⟨t, (parameter_zero_iff Z C z P Q hPQ t).mpr ⟨w.val, rfl⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨w, hw⟩ := (parameter_zero_iff Z C z P Q hPQ t).mp ht
    have hwP : (Open.ClosedImmersionComposition.Constructions.compose Z C).regularComplementInclusion w ∈ P.neighborhood := by
      change Z.regularComplementInclusion (C.regularComplementInclusion w) ∈ P.neighborhood
      rw [hw]
      exact t.property
    exact ⟨⟨w, hwP⟩, Subtype.ext (congrArg Z.regularComplementInclusion hw)⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NestedNormalEquation.Constructions
