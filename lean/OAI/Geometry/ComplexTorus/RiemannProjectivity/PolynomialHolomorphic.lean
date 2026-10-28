import OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothLocal
import OAI.Geometry.ComplexTorus.RiemannProjectivity.IdentityEq
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialDerivative
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Polynomial Holomorphic -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.PolynomialHolomorphic.Constructions.PolynomialHolomorphicGerms

noncomputable section

/-! # RiemannProjectivity: polynomial evaluation in genuine holomorphic germs -/

open Set Filter
open scoped _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ} {ι : Type*} [Fintype ι]

def pullback (x : V) (g : V → ι → ℂ) {U : Set V}
    (hU : IsOpen U) (hx : x ∈ U) (hg : DifferentiableOn ℂ g U) :
    MvPolynomial ι ℂ →+* AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  (((Germ.coeRingHom (𝓝 x)).comp (RingHom.pi (fun y => MvPolynomial.eval (g y)))).codRestrict
    (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.holomorphicGerms x) (fun p =>
      ⟨(fun y => MvPolynomial.eval (g y) p), rfl, U, hU, hx,
        (AlgebraicGeometry.ComplexPoints.Analytic.PolynomialDerivative.differentiable_polynomial_eval p).comp_differentiableOn hg⟩))

theorem pullback_eq_zero (x : V) (g : V → ι → ℂ) {U : Set V}
    (hU : IsOpen U) (hx : x ∈ U) (hg : DifferentiableOn ℂ g U)
    (p : MvPolynomial ι ℂ) :
    pullback x g hU hx hg p = 0 ↔ ∀ᶠ y in 𝓝 x, MvPolynomial.eval (g y) p = 0 := by
  change (⟨_, _⟩ : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) = 0 ↔ _
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

theorem pullback_val (x : V) (g : V → ι → ℂ) {U : Set V}
    (hU : IsOpen U) (hx : x ∈ U) (hg : DifferentiableOn ℂ g U)
    (p : MvPolynomial ι ℂ) :
    (pullback x g hU hx hg p).val =
      ((fun y => MvPolynomial.eval (g y) p) : Germ (𝓝 x) ℂ) := rfl

theorem pullback_value (x : V) (g : V → ι → ℂ) {U : Set V}
    (hU : IsOpen U) (hx : x ∈ U) (hg : DifferentiableOn ℂ g U)
    (p : MvPolynomial ι ℂ) :
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x (pullback x g hU hx hg p) = MvPolynomial.eval (g x) p := rfl

def base (x : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →+* AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  pullback x id isOpen_univ (mem_univ _) differentiable_id.differentiableOn

theorem base_injective (x : Fin n → ℂ) : Function.Injective (base x) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  have hzero : ∀ᶠ y in 𝓝 x, MvPolynomial.eval y p = 0 :=
    (pullback_eq_zero x id isOpen_univ (mem_univ _) differentiable_id.differentiableOn p).mp hp
  apply MvPolynomial.funext
  intro y
  rw [map_zero]
  exact IdentityEq.Constructions.Identity.eq_zero_of_zero_germ isOpen_univ isPreconnected_univ
    (AlgebraicGeometry.ComplexPoints.Analytic.PolynomialDerivative.differentiable_polynomial_eval p).differentiableOn (mem_univ x) hzero y (mem_univ y)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.PolynomialHolomorphic.Constructions.PolynomialHolomorphicGerms
