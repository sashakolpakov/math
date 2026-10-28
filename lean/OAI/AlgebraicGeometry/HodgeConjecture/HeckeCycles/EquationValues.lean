import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationValues
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius

/-! # Equation Values -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EquationValues.CM.Hecke

noncomputable section

/-! Express the native equation in the original special Albanese before
choosing the common field and DVR for a pair of component points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM

variable {E K : Type} [Field E] [NumberField E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K)
  {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
  (R : M.GoodIntegralReduction q j)
  (a : M.Family) (hden : Nat.Coprime q M.arithmetic.denominator)
  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence
    ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (χ : Fin M.s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
  (hg : (Witt.PELSource.CM.heckeData M a C χ).HasIntegralModelGeometry)
  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L]
  [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L] (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C χ
local notation "U" => Over.mk (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationGenericTest.CM.originalBase (L := L) j)
local notation "G" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM.specialAlbanese R a
local notation "Uk" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q
local notation "im" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationData.CM.IntrinsicPoints.image HD hg j hden R.residue R.residue_compatibility V
def originalOperator (f : (HD).EndK) : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (G).X :=
  Intrinsic.EquationData.CM.IntrinsicPoints.operator HD hg j hden R.residue R.residue_compatibility f

local notation "op" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EquationValues.CM.Hecke.originalOperator M j R a hden C χ hg

theorem originalOperator_eq (f : (HD).EndK) :
    Intrinsic.EquationData.CM.IntrinsicPoints.operator HD hg j hden R.residue R.residue_compatibility f = op f := rfl

theorem action_eq (g : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (G).X) :
    ⇑(PointEvaluation.CM.action (ComparisonPolynomial.CM.sourceGroup HD R.residue) Uk g) =
      ⇑(PointEvaluation.CM.action G Uk g) := by
  funext z
  apply Additive.toMul.injective
  exact (PointEvaluation.CM.action_apply
    (ComparisonPolynomial.CM.sourceGroup HD R.residue) Uk g z.toMul).trans
      (PointEvaluation.CM.action_apply G Uk g z.toMul).symm

theorem original_action_eq (f : (HD).EndK) :
    ⇑(PointEvaluation.CM.action (ComparisonPolynomial.CM.sourceGroup HD R.residue) Uk
      (Intrinsic.EquationData.CM.IntrinsicPoints.operator HD hg j hden R.residue R.residue_compatibility f)) =
    ⇑(PointEvaluation.CM.action G Uk (op f)) :=
  (congrArg (fun g => ⇑(PointEvaluation.CM.action
      (ComparisonPolynomial.CM.sourceGroup HD R.residue) Uk g))
    (originalOperator_eq M j R a hden C χ hg f)).trans
      (action_eq M j R a C χ (op f))

theorem equation_values (f : (HD).EndK) (x y : U ⟶ (HD).space)
    (Nx Ny : Multiset (U ⟶ (HD).space))
    (sx sy : Additive (Uk ⟶ (G).X)) (rx ry : Multiset (Additive (Uk ⟶ (G).X)))
    (hx : im x = sx) (hy : im y = sy)
    (hNx : Nx.map im = rx) (hNy : Ny.map im = ry)
    (h : Intrinsic.EquationData.CM.IntrinsicPoints.Equation HD hg j hden R.residue R.residue_compatibility V
      f x y Nx Ny) :
    PointEvaluation.CM.action G Uk (op f) (sx - sy) = rx.sum - ry.sum :=
  (congrFun (original_action_eq M j R a hden C χ hg f) (sx - sy)).symm.trans
    (Intrinsic.EquationValues.CM.IntrinsicPoints.equation_values HD hg j hden R.residue R.residue_compatibility V
      f x y Nx Ny sx sy rx ry hx hy hNx hNy h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EquationValues.CM.Hecke
