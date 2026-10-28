import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationData

/-! # Operator Specialization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OperatorSpecialization.CM

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalNeighbors.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)
  (res : AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ZMod q)
  (hres : res.comp (algebraMap (NumberField.RingOfIntegers K)
    (AbelianScheme.TateComparison.Data.modelRing K D.denominator)) = j.residue)
  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L]
  [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop

theorem operator_eq (f : D.EndK) :
    EquationData.CM.IntrinsicPoints.operator D hg j hcop res hres f =
      Source.Specialization.CM.sourceSpecialization D hg j hcop res hres
        (EndomorphismComparison.CM.integralEquiv (A).variety.scheme f) :=
  (EquationData.CM.IntrinsicPoints.specialization_eq D hg j hcop res hres f).symm.trans
    ((Source.SpecialEnd.CM.sourceData_specialization_apply D hg j hcop res hres
      (Source.LocalNeighbors.CM.rawEnd D hg j hcop f).generic).trans
      (congrArg (Source.Specialization.CM.sourceSpecialization D hg j hcop res hres)
        (Source.LocalNeighbors.CM.rawEnd_algebraic_generic D hg j hcop f)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OperatorSpecialization.CM
