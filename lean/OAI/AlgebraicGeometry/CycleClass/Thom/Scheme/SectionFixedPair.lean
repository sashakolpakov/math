import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionNormalPair
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothNormalReindex

/-! # Section Fixed Pair -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionFixedPair.Constructions

noncomputable section

/-! Actual smooth section normal coordinates in the canonical one-dimensional
complex normal model, for arbitrary smooth integral complex schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothNormalReindex.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionNormalPair.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

theorem exists_native_section_fixedNormalPair_smooth (U : X.left.Opens) (hU : IsAffineOpen U)
    (p b : Γ(X.left, U)) (hp : p ≠ 0)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (x : SectionEvaluation.Constructions.analyticOpen X U) (hxp : SectionEvaluation.Constructions.sectionEvaluationOn X U p x = 0)
    (hxb : SectionEvaluation.Constructions.sectionEvaluationOn X U b x ≠ 0) :
    ∃ (d : ℕ) (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin 1 → ℂ)
      (fun z : {y : SectionEvaluation.Constructions.analyticOpen X U // SectionEvaluation.Constructions.sectionEvaluationOn X U p y = 0} => z.val.val) ⟨x, hxp⟩),
      ∃ hPU : P.neighborhood ⊆ (SectionEvaluation.Constructions.analyticOpen X U : Set _),
      d + 1 = Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom ∧
      P.ambientChart.MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, (Fin d → ℂ) × (Fin 1 → ℂ)) ∧
      ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, (Fin d → ℂ) × (Fin 1 → ℂ))
        ∞ P.ambientChart P.ambientChart.source ∧
      ContMDiffOn 𝓘(ℂ, (Fin d → ℂ) × (Fin 1 → ℂ)) 𝓘(ℂ, E)
        ∞ P.ambientChart.symm P.ambientChart.target ∧
      ∀ y : P.neighborhood, P.normalCoordinate y 0 =
        SectionEvaluation.Constructions.sectionEvaluationOn X U p ⟨y.val, hPU y.property⟩ := by
  obtain ⟨d, P, hPU, hd, hmd, hq, hqi, hcoord⟩ :=
    SectionNormalPair.Constructions.exists_native_section_normalPair_smooth X U hU p b hp hsm x hxp hxb
  let T := HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.normalPairReindex P HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.planeCoordinates HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.planeCoordinates_norm
  have hTP : T.neighborhood ⊆ P.neighborhood :=
    (HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.normalPairReindex_neighborhood P HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.planeCoordinates HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.planeCoordinates_norm).subset
  have hTU : T.neighborhood ⊆ (SectionEvaluation.Constructions.analyticOpen X U : Set _) := fun _ hy => hPU (hTP hy)
  have hTd := HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.normalPairReindex_mdifferentiable P HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.planeCoordinates HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.planeCoordinates_norm hmd
  have hTs := HodgeConjecture.DegreeTwo.SmoothNormalReindex.Constructions.normalPairReindex_smooth P HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.planeCoordinates HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.planeCoordinates_norm hq hqi
  refine ⟨d, T, hTU, hd, hTd, hTs.1, hTs.2, ?_⟩
  intro y
  change HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.planeCoordinates (P.ambientChart y.val).2 0 = _
  exact hcoord ⟨y.val, hTP y.property⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionFixedPair.Constructions
