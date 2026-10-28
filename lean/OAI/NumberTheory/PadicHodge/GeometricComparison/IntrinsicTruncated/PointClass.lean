import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.SmallTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSectionClass

/-! # Point Class -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The original scalar point quotient gives the trace-one class on
the exact native affine cover used by the finite-level comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq) (n : ℕ)

def Geometry.AbelianH1Model.truncatedSerrePointClass := IntegralComparison.Smooth.ProjectiveSectionClassData.sectionClass
  (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
  (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
  (A.truncatedTraceDimension n + 2) le_rfl A.dimension

theorem Geometry.AbelianH1Model.truncatedSerrePointClass_trace :
    IntegralComparison.Smooth.ProjectiveFormTrace.trace (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
      (A.truncatedTraceDimension n + 2) le_rfl A.dimension (A.truncatedSerrePointClass n) = 1 :=
  IntegralComparison.Smooth.ProjectiveSectionClass.trace_one
    (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    (A.truncatedTraceDimension n + 2) le_rfl A.dimension

def Geometry.AbelianH1Model.truncatedTracePointClass : A.TruncatedTopFormCohomology n :=
  (IntegralComparison.Intrinsic.TopFormTrace.serreIso (A.truncatedModel n).scheme
    (A.truncatedTraceMorphism n) A.dimension).inv (A.truncatedSerrePointClass n)

theorem Geometry.AbelianH1Model.truncatedTracePointClass_serre :
    (IntegralComparison.Intrinsic.TopFormTrace.serreIso (A.truncatedModel n).scheme
      (A.truncatedTraceMorphism n) A.dimension).hom (A.truncatedTracePointClass n) =
      A.truncatedSerrePointClass n :=
  ConcreteCategory.congr_hom
    (IntegralComparison.Intrinsic.TopFormTrace.serreIso (A.truncatedModel n).scheme
      (A.truncatedTraceMorphism n) A.dimension).inv_hom_id (A.truncatedSerrePointClass n)

theorem Geometry.AbelianH1Model.truncatedTracePointClass_trace : A.truncatedTopFormTrace n (A.truncatedTracePointClass n) = 1 := by
  rw [A.truncatedTopFormTrace_eq]
  change IntegralComparison.Smooth.ProjectiveFormTrace.trace (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedTraceDimension n + 2) le_rfl A.dimension
    ((IntegralComparison.Intrinsic.TopFormTrace.serreIso (A.truncatedModel n).scheme
      (A.truncatedTraceMorphism n) A.dimension).hom (A.truncatedTracePointClass n)) = 1
  rw [A.truncatedTracePointClass_serre]
  exact A.truncatedSerrePointClass_trace n

variable (hpos : 0 < A.dimension)

def Geometry.AbelianH1Model.truncatedSmallPointClass : A.TruncatedSmallTopForms n :=
  (A.truncatedTopFormCoverIso n hpos).symm (A.truncatedTracePointClass n)

theorem Geometry.AbelianH1Model.truncatedSmallPointClass_cover :
    A.truncatedTopFormCoverIso n hpos (A.truncatedSmallPointClass n hpos) =
      A.truncatedTracePointClass n :=
  (A.truncatedTopFormCoverIso n hpos).apply_symm_apply _

theorem Geometry.AbelianH1Model.truncatedSmallPointClass_trace :
    A.truncatedSmallTopFormTrace n hpos (A.truncatedSmallPointClass n hpos) = 1 := by
  change A.truncatedTopFormTrace n
    (A.truncatedTopFormCoverIso n hpos (A.truncatedSmallPointClass n hpos)) = 1
  rw [A.truncatedSmallPointClass_cover]
  exact A.truncatedTracePointClass_trace n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
