import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.GermMaps
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Multivariable Polynomial Germs -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.MultivariablePolynomialGerms.AnalyticLocal

noncomputable section

/-! Actual evaluation of multivariable complex polynomials in the
holomorphic local ring, normalized on polynomial functions. -/

open Set Filter
open scoped _root_.Topology

variable {ι : Type*} [Fintype ι]

def coordinateFunctionGerm (x : ι → ℂ) (i : ι) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction x (fun y => y i) isOpen_univ (mem_univ x) (differentiable_apply i).differentiableOn

def mvPolynomialGermMap (x : ι → ℂ) : MvPolynomial ι ℂ →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  MvPolynomial.eval₂Hom (Holomorphic.GermMaps.AnalyticLocal.holomorphicConstantHom x) (coordinateFunctionGerm x)

theorem mvPolynomialGermMap_C (x : ι → ℂ) (c : ℂ) :
    mvPolynomialGermMap x (MvPolynomial.C c) = Holomorphic.GermMaps.AnalyticLocal.holomorphicConstantHom x c :=
  MvPolynomial.eval₂Hom_C _ _ _

theorem mvPolynomialGermMap_X (x : ι → ℂ) (i : ι) :
    mvPolynomialGermMap x (MvPolynomial.X i) = coordinateFunctionGerm x i :=
  MvPolynomial.eval₂Hom_X' _ _ _

theorem mvPolynomialGermMap_val (x : ι → ℂ) (P : MvPolynomial ι ℂ) :
    (mvPolynomialGermMap x P).val =
      ((fun y : ι → ℂ => MvPolynomial.eval y P) : Germ (𝓝 x) ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [mvPolynomialGermMap_C]
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun _ => (MvPolynomial.eval_C c).symm)
  | add P Q hP hQ =>
    rw [map_add]
    change (mvPolynomialGermMap x P).val + (mvPolynomialGermMap x Q).val = _
    rw [hP, hQ]
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun _ => MvPolynomial.eval_add.symm)
  | mul_X P i hP =>
    rw [map_mul, mvPolynomialGermMap_X]
    change (mvPolynomialGermMap x P).val *
      ((fun y : ι → ℂ => y i) : Germ (𝓝 x) ℂ) = _
    rw [hP]
    apply Germ.coe_eq.mpr
    apply Filter.Eventually.of_forall
    intro y
    change MvPolynomial.eval y P * y i = MvPolynomial.eval y (P * MvPolynomial.X i)
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]

theorem mvPolynomialGermMap_value (x : ι → ℂ) (P : MvPolynomial ι ℂ) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x (mvPolynomialGermMap x P) = MvPolynomial.eval x P := by
  exact congrArg Germ.value (mvPolynomialGermMap_val x P)

end

end OAI.AlgebraicGeometry.Comparison.Betti.MultivariablePolynomialGerms.AnalyticLocal
