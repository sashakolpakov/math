import OAI.AlgebraicTopology.Duality.Poincare.RationalizedChainClasses
import OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison

/-! # Chain Representatives -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ChainRepresentatives

noncomputable section

/-! Actual coefficient change of explicit integral singular-chain representatives. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def rationalSingularChainElement (X : TopCat.{0}) (n : ℕ)
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X n :=
  (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] z)

theorem rationalSingularChainElement_add (X : TopCat.{0}) (n : ℕ)
    (z w : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    rationalSingularChainElement X n (z + w) =
      rationalSingularChainElement X n z + rationalSingularChainElement X n w := by
  simp only [rationalSingularChainElement, TensorProduct.tmul_add, map_add]

theorem rationalSingularChainElement_sub (X : TopCat.{0}) (n : ℕ)
    (z w : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    rationalSingularChainElement X n (z - w) =
      rationalSingularChainElement X n z - rationalSingularChainElement X n w := by
  simp only [rationalSingularChainElement, TensorProduct.tmul_sub, map_sub]

theorem rationalSingularChainElement_zsmul (X : TopCat.{0}) (n : ℕ)
    (a : ℤ) (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    rationalSingularChainElement X n (a • z) = a • rationalSingularChainElement X n z := by
  change (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n
    ((TensorProduct.mk ℤ ℚ ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) 1) (a • z)) = _
  rw [map_zsmul, map_zsmul]
  rfl

theorem rationalSingularChainElement_d (X : TopCat.{0}) (i j : ℕ)
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X i) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d i j (rationalSingularChainElement X i z) =
      rationalSingularChainElement X j ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d i j z) :=
  ConcreteCategory.congr_hom ((CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.comm i j)
    ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] z)

theorem rationalSingularChainElement_map {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map f).f n (rationalSingularChainElement X n z) =
      rationalSingularChainElement Y n ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f n z) := by
  have hn := congrArg
    (fun g : CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) ⟶ AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y => g.f n)
    (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso_hom_naturality f)
  have h := ConcreteCategory.congr_hom hn
    (show (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X)).X n from
      (1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] z)
  exact h.symm

def rationalSingularCycle (X : TopCat.{0}) (n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n) : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) n :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom n (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n 1 z)

theorem rationalSingularCycle_val (X : TopCat.{0}) (n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n) :
    (rationalSingularCycle X n z).val = rationalSingularChainElement X n z.val := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ChainRepresentatives
