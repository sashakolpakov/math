import OAI.Geometry.ComplexTorus.RiemannProjectivity.PolynomialHolomorphic
import OAI.Geometry.ComplexTorus.RiemannProjectivity.EquationAlgebraicityIs

/-! # Graph Germs On -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.GraphGermsOn.Constructions.GraphGerms

noncomputable section

/-! # RiemannProjectivity: the equation algebra maps to its genuine holomorphic branch -/

open Set Filter _root_.Polynomial
open scoped _root_.Topology
open OAI.Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SmoothEquationPoint OAI.Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SplitPolynomialJacobian

variable {n m : ℕ}

def graph (ψ : (Fin n → ℂ) → Fin m → ℂ) (y : Fin n → ℂ) : Fin n ⊕ Fin m → ℂ :=
  Sum.elim y (ψ y)

theorem differentiableOn_graph (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hψ : DifferentiableOn ℂ ψ U) : DifferentiableOn ℂ (graph ψ) U := by
  intro y hy
  apply differentiableWithinAt_pi.mpr
  intro i
  cases i with
  | inl i => exact differentiableAt_apply i y |>.differentiableWithinAt
  | inr i => exact differentiableWithinAt_pi.mp (hψ y hy) i

def polynomialMap (x : Fin n → ℂ) (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hx : x ∈ U) (hψ : DifferentiableOn ℂ ψ U) :
    MvPolynomial (Fin n ⊕ Fin m) ℂ →+* AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  PolynomialHolomorphic.Constructions.PolynomialHolomorphicGerms.pullback x (graph ψ) hU hx (differentiableOn_graph ψ hψ)

theorem polynomialMap_base (x : Fin n → ℂ) (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hx : x ∈ U) (hψ : DifferentiableOn ℂ ψ U) :
    (polynomialMap x ψ hU hx hψ).comp (MvPolynomial.rename Sum.inl).toRingHom =
      PolynomialHolomorphic.Constructions.PolynomialHolomorphicGerms.base x := by
  apply RingHom.ext
  intro p
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall (fun y => by
    simp [graph, MvPolynomial.eval_rename, Function.comp_def])

instance germAlgebra (x : Fin n → ℂ) :
    Algebra (MvPolynomial (Fin n) ℂ) (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) :=
  (PolynomialHolomorphic.Constructions.PolynomialHolomorphicGerms.base x).toAlgebra

def equationMap (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Fin n → ℂ) (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hx : x ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hzero : ∀ y ∈ U, ∀ j, (F j).eval₂ (MvPolynomial.eval y) (ψ y j) = 0) :
    JacobianLocalizationAt.Constructions.SmoothEquationPoint.equationRing F →ₐ[MvPolynomial (Fin n) ℂ] AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  { Ideal.Quotient.lift _ (polynomialMap x ψ hU hx hψ) (by
      change Ideal.span _ ≤ RingHom.ker (polynomialMap x ψ hU hx hψ)
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      apply (PolynomialHolomorphic.Constructions.PolynomialHolomorphicGerms.pullback_eq_zero x (graph ψ) hU hx
        (differentiableOn_graph ψ hψ) (JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation j (F j))).mpr
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.eval_equation j (F j) y (ψ y)).trans (hzero y hy j)) with
    commutes' p := by
      change polynomialMap x ψ hU hx hψ ((MvPolynomial.rename Sum.inl) p) =
        PolynomialHolomorphic.Constructions.PolynomialHolomorphicGerms.base x p
      exact congrArg (fun f : MvPolynomial (Fin n) ℂ →+* AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x => f p)
        (polynomialMap_base x ψ hU hx hψ) }

theorem equationMap_value (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Fin n → ℂ) (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hx : x ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hzero : ∀ y ∈ U, ∀ j, (F j).eval₂ (MvPolynomial.eval y) (ψ y j) = 0) :
    (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x).comp (equationMap F x ψ hU hx hψ hzero).toRingHom =
      (JacobianLocalizationAt.Constructions.SmoothEquationPoint.point F x (ψ x) (hzero x hx)).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  rfl

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.GraphGermsOn.Constructions.GraphGerms
