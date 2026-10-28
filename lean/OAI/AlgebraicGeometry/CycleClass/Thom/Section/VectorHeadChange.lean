import OAI.AlgebraicGeometry.CycleClass.Thom.ElementaryEquationHomotopy
import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Vector Head Change -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions

noncomputable section

/-! Elementary changes of actual regular-section equations preserve
their relative cohomology pullback. The homotopy condition is derived
from membership in the genuine tail section ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.ElementaryEquationHomotopy.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)

def sectionVectorEquation (n : ℕ) (s : Fin n → Γ(Y.left, ⊤)) :
    TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) ⟶ TopCat.of (Fin n → ℂ) :=
  TopCat.ofHom ⟨fun x i => DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x (s i),
    continuous_pi (fun i => DivisorClass.Chern.AnalyticTransitions.Construction.continuous_globalSectionEvaluation Y (s i))⟩

def sectionScalarEquation (s : Γ(Y.left, ⊤)) : TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) ⟶ TopCat.of ℂ :=
  TopCat.ofHom (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionContinuousMap Y s)

variable (n : ℕ) (r : Γ(Y.left, ⊤)) (s : Fin n → Γ(Y.left, ⊤)) (a : Γ(Y.left, ⊤))

theorem adjustedEquation_eq_sectionVector :
    ElementaryEquationHomotopy.Constructions.adjustedEquation n (sectionVectorEquation Y (n + 1) (Fin.cons r s)) (sectionScalarEquation Y a) =
      sectionVectorEquation Y (n + 1) (Fin.cons (r + a) s) := by
  ext x : 1
  ext i
  cases i using Fin.cases with
  | zero => exact (map_add (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x) r a).symm
  | succ i => rfl

include s in
theorem tailIdeal_evaluation_zero (ha : a ∈ Ideal.span (Set.range s)) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (hz : ∀ i, DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x (s i) = 0) : DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x a = 0 := by
  have hle : Ideal.span (Set.range s) ≤ RingHom.ker (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hz i
  exact hle ha

theorem sectionVector_zero_iff_head_change (ha : a ∈ Ideal.span (Set.range s)) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :
    sectionVectorEquation Y (n + 1) (Fin.cons (r + a) s) x = 0 ↔
      sectionVectorEquation Y (n + 1) (Fin.cons r s) x = 0 := by
  have he := (ElementaryEquationHomotopy.Constructions.headHomotopy n (sectionVectorEquation Y (n + 1) (Fin.cons r s))
    (sectionScalarEquation Y a)).map_one_left x
  have he' := he.trans (congrArg (fun f => f x) (adjustedEquation_eq_sectionVector Y n r s a))
  exact (iff_of_eq (congrArg (fun v => v = 0) he').symm).trans
    (ElementaryEquationHomotopy.Constructions.headHomotopy_zero_iff n (sectionVectorEquation Y (n + 1) (Fin.cons r s)) (sectionScalarEquation Y a)
      (fun y hy => tailIdeal_evaluation_zero Y n s a ha y hy) 1 x)

theorem relativeCohomologyMap_section_head_change (ha : a ∈ Ideal.span (Set.range s))
    (A : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (hf : Set.MapsTo (sectionVectorEquation Y (n + 1) (Fin.cons r s)) A ({0} : Set (Fin (n + 1) → ℂ))ᶜ)
    (hg : Set.MapsTo (sectionVectorEquation Y (n + 1) (Fin.cons (r + a) s)) A ({0} : Set (Fin (n + 1) → ℂ))ᶜ)
    (d : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (sectionVectorEquation Y (n + 1) (Fin.cons r s)) hf d =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (sectionVectorEquation Y (n + 1) (Fin.cons (r + a) s)) hg d := by
  let hzero := fun y hy => tailIdeal_evaluation_zero Y n s a ha y hy
  exact (ElementaryEquationHomotopy.Constructions.relativeCohomologyMap_head_adjustment n (sectionVectorEquation Y (n + 1) (Fin.cons r s))
    (sectionScalarEquation Y a) hzero A hf d).trans
    (ThomOpenRestriction.Constructions.pairMap_congr (adjustedEquation_eq_sectionVector Y n r s a) _ hg d)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions
