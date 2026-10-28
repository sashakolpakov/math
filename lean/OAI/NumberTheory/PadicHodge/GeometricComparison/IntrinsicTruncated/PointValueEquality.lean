import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedPointValues
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedChartExistence
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.FiniteResidueChoice

/-! # Point Value Equality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The two original point values agree, with every chart, support,
component numerator and common scalar chosen from the native model. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m)

theorem Geometry.AbelianH1Model.truncatedPointValue_equality :
    A.truncatedFinitePointValue n m hm = A.truncatedOrdinaryPointValue n := by
  obtain ⟨U,hU,D,hgood,⟨P⟩⟩ := A.exists_truncatedPairedPointChart n m hm
  obtain ⟨j,z,hz,he,_,_,hV,hj,_,_⟩ :=
    P.exists_finiteResidue hgood (A.truncatedTraceDimension n+2) le_rfl
  have hz' : Geometry.AbelianH1Model.TruncatedPairedPointParameters.IsComponent P z := by
    convert hz using 1
    as_aux_lemma => rfl
  exact Geometry.AbelianH1Model.TruncatedPairedPointParameters.equality P z (P.final_good hgood) hz' he hV j hj

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
