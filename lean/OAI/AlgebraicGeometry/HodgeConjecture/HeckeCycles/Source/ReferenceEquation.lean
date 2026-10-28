import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalNeighbors
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceLocalEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEvaluation

/-! # Reference Equation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ReferenceEquation.CM.Reference

noncomputable section

/-! The actual evaluated TateComparison endomorphism equation becomes the local
equation on the original source's canonical inverse images. The operator
is the same extending endomorphism used by the comparison realization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalNeighbors.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceLocalEquation.CM.Reference OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator) (T : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q]))

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop
local notation "M" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM.nativeSource D hg j hcop
local notation "jq" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.localFieldEmbedding j)

theorem local_equation_of_original_evaluation (f : D.EndK)
    (x y : (Over.map jq).obj T ⟶ D.space)
    (Nx Ny : Multiset ((Over.map jq).obj T ⟶ D.space))
    (h : ReferenceLocalEquation.CM.Reference.OriginalEquation A M T (D.albaneseMap hg)
      (PointSpecializationFormula.CM.Points.evaluateAt D.albaneseGroup ((Over.map jq).obj T) f) x y Nx Ny) :
    ReferenceLocalEquation.CM.Reference.LocalOriginalEquation A M T (LocalNeighbors.CM.rawEnd D hg j hcop f) x y Nx Ny := by
  apply ReferenceLocalEquation.CM.Reference.local_from_original A M T (LocalNeighbors.CM.rawEnd D hg j hcop f)
    (D.albaneseMap hg) (AlbaneseMapCompatibility.CM.genericMap_eq D hg j hcop)
    (PointSpecializationFormula.CM.Points.evaluateAt D.albaneseGroup ((Over.map jq).obj T) f)
  · intro z
    exact (LocalNeighbors.CM.rawPoint_evaluation D hg j hcop T f z).trans
      (TateComparisonPointEvaluation.CM.evaluate_eq_endPoint D f z).symm
  · exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ReferenceEquation.CM.Reference
