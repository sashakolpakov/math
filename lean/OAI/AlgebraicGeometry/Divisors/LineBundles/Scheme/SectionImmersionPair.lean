import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionFixedPair
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairReindex
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SectionClassPullback
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion

/-! # Section Immersion Pair -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SectionImmersionPair.BundleCycles

noncomputable section

/-! A smooth local scheme equation provides normal coordinates for the actual closed immersion, retaining the literal global section as normal coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionFixedPair.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions

variable {Y X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral X.left] [Smooth X.hom] (i : Y ⟶ X) [IsClosedImmersion i.left]
  (s : Γ(X.left, ⊤))
  (hzero : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) = Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage X s))
  (hd : Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom + 1 =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)

include hzero hd in
omit [Smooth Y.hom] [IsClosedImmersion (Over.Hom.left i)] in
theorem schemeSectionImmersion_exists_normalPair
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (U : X.left.Opens) (hU : IsAffineOpen U)
    (hxU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x ∈ CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X U)
    (hs : X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s ≠ 0)
    (b : Γ(X.left, U))
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk
        (Ideal.span {X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s}) b)))
    (hb : CycleClass.Thom.Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X U b ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x, hxU⟩ ≠ 0) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)
        (Fin 1 → ℂ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) x,
      P.ambientChart.MDifferentiable
        𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
        𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) × (Fin 1 → ℂ)) ∧
      ∀ y : P.neighborhood, P.normalCoordinate y = CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation X s y.val := by
  let sU := X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s
  have hx0 : CycleClass.Thom.Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X U sU ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x, hxU⟩ = 0 := by
    rw [CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.sectionEvaluationOn_globalRestriction]
    have hz := (Set.ext_iff.mp hzero (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x)).mp (Set.mem_range_self x)
    rw [CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range] at hz
    exact hz
  obtain ⟨d, P, hPU, hdim, hP, _, _, hcoord⟩ :=
    CycleClass.Thom.Scheme.SectionFixedPair.Constructions.exists_native_section_fixedNormalPair_smooth X U hU sU b hs hsm
      ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x, hxU⟩ hx0 hb
  have hd' : d = Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom := by omega
  subst d
  have hr : ∀ y ∈ P.neighborhood, y ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ↔
      y ∈ Set.range (fun z : {y : CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X U // CycleClass.Thom.Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X U sU y = 0} => z.val.val) := by
    intro y hy
    rw [hzero, CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range]
    constructor
    · intro hz
      refine ⟨⟨⟨y, hPU hy⟩, ?_⟩, rfl⟩
      exact (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.sectionEvaluationOn_globalRestriction X U s ⟨y, hPU hy⟩).trans hz
    · rintro ⟨z, rfl⟩
      exact (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.sectionEvaluationOn_globalRestriction X U s z.val).symm.trans z.property
  let Q := HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.normalPairReplaceSupport P (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) x rfl hr
  refine ⟨Q, hP, ?_⟩
  intro y
  ext a
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  exact (hcoord y).trans (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.sectionEvaluationOn_globalRestriction X U s ⟨y.val, hPU y.property⟩)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SectionImmersionPair.BundleCycles
