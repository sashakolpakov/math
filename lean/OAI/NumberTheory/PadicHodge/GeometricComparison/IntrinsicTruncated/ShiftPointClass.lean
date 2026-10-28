import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftSerreTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionClass

/-! # Shift Point Class -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The original finite-coefficient fixed point class is precisely the
trace-normalized class on the native common source cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m)

def Geometry.AbelianH1Model.truncatedShiftSerrePointClass := IntegralComparison.FiniteEtale.SectionClassData.sectionClass
  (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
  (A.truncatedTraceMorphism n) (A.truncatedShiftIdentitySection n m hm)
  (A.truncatedShiftIdentitySection_over n m hm) (A.truncatedTraceDimension n + 2) le_rfl A.dimension

theorem Geometry.AbelianH1Model.truncatedShiftSerrePointClass_trace :
    IntegralComparison.FiniteEtale.ProperTraceBase.trace (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm)
      (A.truncatedShiftOver n m hm) (A.truncatedTraceMorphism n)
      (A.truncatedTraceDimension n + 2) le_rfl A.dimension
      (A.truncatedShiftSerrePointClass n m hm) = 1 :=
  IntegralComparison.FiniteEtale.SectionClass.trace_one
    (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
    (A.truncatedTraceMorphism n) (A.truncatedShiftIdentitySection n m hm)
    (A.truncatedShiftIdentitySection_over n m hm) (A.truncatedTraceDimension n + 2) le_rfl A.dimension

variable (hpos : 0 < A.dimension)

def Geometry.AbelianH1Model.truncatedShiftPointClass : A.TruncatedShiftCommonTopForms n m hm :=
  (A.truncatedShiftCommonSerreIso n m hm hpos).inv (A.truncatedShiftSerrePointClass n m hm)

theorem Geometry.AbelianH1Model.truncatedShiftPointClass_serre :
    (A.truncatedShiftCommonSerreIso n m hm hpos).hom
      (A.truncatedShiftPointClass n m hm hpos) = A.truncatedShiftSerrePointClass n m hm :=
  ConcreteCategory.congr_hom (A.truncatedShiftCommonSerreIso n m hm hpos).inv_hom_id
    (A.truncatedShiftSerrePointClass n m hm)

theorem Geometry.AbelianH1Model.truncatedShiftPointClass_trace :
    A.truncatedShiftCommonTraceEquiv n m hm hpos (A.truncatedShiftPointClass n m hm hpos) = 1 := by
  rw [A.truncatedShiftCommonTraceEquiv_serre, A.truncatedShiftPointClass_serre]
  exact A.truncatedShiftSerrePointClass_trace n m hm

theorem Geometry.AbelianH1Model.truncatedShiftPointClass_normalized :
    A.truncatedShiftPointClass n m hm hpos = (A.truncatedShiftCommonTraceEquiv n m hm hpos).symm 1 := by
  apply (A.truncatedShiftCommonTraceEquiv n m hm hpos).injective
  exact (A.truncatedShiftPointClass_trace n m hm hpos).trans
    ((A.truncatedShiftCommonTraceEquiv n m hm hpos).apply_symm_apply 1).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
