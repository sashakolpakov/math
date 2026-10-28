import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionChart
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedNormalPair

/-! # Section Normal Pair -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionNormalPair.Constructions

noncomputable section

/-!
# ThomClass: native complex normal pairs for actual scheme divisors

The support is the full zero locus on the original algebraic open, mapped
into the whole native analytic scheme. Its actual section is the normal
coordinate, and the chart is complex differentiable in both directions.
-/

open scoped ContDiff _root_.Topology _root_.Manifold
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedNormalPair.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionChart.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

/-- Actual scheme-section divisors admit complex differentiable normal
pairs inside their original open, with the proved codimension one. -/
theorem exists_native_section_normalPair_smooth (U : X.left.Opens) (hU : IsAffineOpen U)
    (p b : Γ(X.left, U)) (hp : p ≠ 0)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (x : SectionEvaluation.Constructions.analyticOpen X U) (hxp : SectionEvaluation.Constructions.sectionEvaluationOn X U p x = 0)
    (hxb : SectionEvaluation.Constructions.sectionEvaluationOn X U b x ≠ 0) :
    ∃ (d : ℕ) (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) ℂ
      (fun z : {y : SectionEvaluation.Constructions.analyticOpen X U // SectionEvaluation.Constructions.sectionEvaluationOn X U p y = 0} => z.val.val)
      ⟨x, hxp⟩),
      ∃ hPU : P.neighborhood ⊆ (SectionEvaluation.Constructions.analyticOpen X U : Set _),
      d + 1 = Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom ∧
      P.ambientChart.MDifferentiable
        𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
        𝓘(ℂ, (Fin d → ℂ) × ℂ) ∧
      ContMDiffOn 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
        𝓘(ℂ, (Fin d → ℂ) × ℂ) ∞ P.ambientChart P.ambientChart.source ∧
      ContMDiffOn 𝓘(ℂ, (Fin d → ℂ) × ℂ)
        𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
        ∞ P.ambientChart.symm P.ambientChart.target ∧
      ∀ y : P.neighborhood, P.normalCoordinate y =
        SectionEvaluation.Constructions.sectionEvaluationOn X U p ⟨y.val, hPU y.property⟩ := by
  obtain ⟨e, q, hxq, hqx, hqU, hq, hqd, hqf, hqi⟩ :=
    SectionChart.Constructions.exists_native_section_chart_smooth X U hU p b hp hsm x hxp hxb
  let D := (fderiv ℂ (fun z => e.symm z p)
    (e ((SectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU).symm x))).ker
  let d := Module.finrank ℂ D
  let c : D ≃L[ℂ] (Fin d → ℂ) := (Module.finBasis ℂ D).equivFun.toContinuousLinearEquiv
  let k : (ℂ × D) ≃L[ℂ] ((Fin d → ℂ) × ℂ) :=
    ((LinearEquiv.prodComm ℂ ℂ D).trans
      (c.toLinearEquiv.prodCongr (LinearEquiv.refl ℂ ℂ))).toContinuousLinearEquiv
  let r := q.transHomeomorph k.toHomeomorph
  have hrx : r x.val = 0 := by
    change k (q x.val) = 0
    rw [hqx, map_zero]
  have hkd : k.toHomeomorph.toOpenPartialHomeomorph.MDifferentiable
      𝓘(ℂ, ℂ × D) 𝓘(ℂ, (Fin d → ℂ) × ℂ) :=
    ⟨(k.contDiff (n := 1)).contMDiff.mdifferentiable one_ne_zero |>.mdifferentiableOn,
      (k.symm.contDiff (n := 1)).contMDiff.mdifferentiable one_ne_zero |>.mdifferentiableOn⟩
  have hrd : r.MDifferentiable
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      𝓘(ℂ, (Fin d → ℂ) × ℂ) := by
    change (q.transHomeomorph k.toHomeomorph).MDifferentiable _ _
    rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
    exact hqd.trans hkd
  have hrf : ContMDiffOn
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      𝓘(ℂ, (Fin d → ℂ) × ℂ) ∞ r r.source :=
    (k.contDiff (n := ∞)).contMDiff.comp_contMDiffOn hqf
  have hri : ContMDiffOn 𝓘(ℂ, (Fin d → ℂ) × ℂ)
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      ∞ r.symm r.target :=
    hqi.comp (k.symm.contDiff (n := ∞)).contMDiff.contMDiffOn (fun _ hz => hz)
  have hdim := (hqd.mfderiv hxq).toLinearEquiv.finrank_eq
  change Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) =
    Module.finrank ℂ (ℂ × D) at hdim
  have hd : d + 1 = Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom := by
    have hdim' : Module.finrank ℂ (ℂ × D) =
        Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) :=
      hdim.symm
    erw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun] at hdim'
    change Module.finrank ℂ D + 1 = _
    omega
  let j := fun z : {y : SectionEvaluation.Constructions.analyticOpen X U // SectionEvaluation.Constructions.sectionEvaluationOn X U p y = 0} => z.val.val
  have hrange : ∀ y ∈ r.source, y ∈ Set.range j ↔ (r y).2 = 0 := by
    intro y hy
    have hcoord := hq ⟨y, hqU hy⟩ hy
    change (r y).2 = SectionEvaluation.Constructions.sectionEvaluationOn X U p ⟨y, hqU hy⟩ at hcoord
    rw [hcoord]
    constructor
    · rintro ⟨z, rfl⟩
      exact z.property
    · intro hpz
      exact ⟨⟨⟨y, hqU hy⟩, hpz⟩, rfl⟩
  obtain ⟨P, hchart⟩ := HodgeConjecture.DegreeTwo.SupportedNormalPair.Constructions.exists_supported_normalPair j ⟨x, hxp⟩ r hxq hrx hrange
  have hPU : P.neighborhood ⊆ (SectionEvaluation.Constructions.analyticOpen X U : Set _) := by
    intro y hy
    have hs := P.neighborhood_subset_source hy
    rw [hchart] at hs
    exact hqU hs
  refine ⟨d, P, hPU, hd, ?_, ?_, ?_, ?_⟩
  · rw [hchart]
    exact hrd
  · rw [hchart]
    exact hrf
  · rw [hchart]
    exact hri
  · intro y
    have hs := P.neighborhood_subset_source y.property
    rw [hchart] at hs
    rw [P.normalCoordinate_apply, hchart]
    exact hq ⟨y.val, hPU y.property⟩ hs

/-- The native complex differentiability consequence of the proved
smooth normal-pair construction. -/
theorem exists_native_section_normalPair (U : X.left.Opens) (hU : IsAffineOpen U)
    (p b : Γ(X.left, U)) (hp : p ≠ 0)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (x : SectionEvaluation.Constructions.analyticOpen X U) (hxp : SectionEvaluation.Constructions.sectionEvaluationOn X U p x = 0)
    (hxb : SectionEvaluation.Constructions.sectionEvaluationOn X U b x ≠ 0) :
    ∃ (d : ℕ) (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) ℂ
      (fun z : {y : SectionEvaluation.Constructions.analyticOpen X U // SectionEvaluation.Constructions.sectionEvaluationOn X U p y = 0} => z.val.val)
      ⟨x, hxp⟩),
      ∃ hPU : P.neighborhood ⊆ (SectionEvaluation.Constructions.analyticOpen X U : Set _),
      d + 1 = Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom ∧
      P.ambientChart.MDifferentiable
        𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
        𝓘(ℂ, (Fin d → ℂ) × ℂ) ∧
      ∀ y : P.neighborhood, P.normalCoordinate y =
        SectionEvaluation.Constructions.sectionEvaluationOn X U p ⟨y.val, hPU y.property⟩ := by
  obtain ⟨d, P, hPU, hd, hmd, _, _, hcoord⟩ :=
    exists_native_section_normalPair_smooth X U hU p b hp hsm x hxp hxb
  exact ⟨d, P, hPU, hd, hmd, hcoord⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionNormalPair.Constructions
