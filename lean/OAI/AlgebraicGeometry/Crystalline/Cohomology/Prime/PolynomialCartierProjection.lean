import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.MultivariableWeightProjection

/-! # Polynomial Cartier Projection -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialCartierProjection.PrimePolynomialCartierProjection

noncomputable section

/-!
# The integral Cartier-weight projection on actual polynomial forms

Composing the coordinate homotopies over the finite coordinate set
retains exactly the monomial forms whose coordinate weights are all
divisible by p. The projection is homotopic to the identity, also on
the original generators-and-relations de Rham complex.
-/

open _root_.CategoryTheory Classical
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [Fintype σ]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomialComplex W σ

def coordinateList : List σ := Finset.univ.toList

def projection : K ⟶ K := MultivariableKoszul.PrimeMultivariableKoszul.successive p k σ (coordinateList σ)

def homotopy : Homotopy (𝟙 K) (projection p k σ) :=
  MultivariableKoszul.PrimeMultivariableKoszul.successiveHomotopy p k σ (coordinateList σ)

theorem projection_word (n : ℕ) (d : σ →₀ ℕ) (a : W) (v : Fin n → σ) :
    (projection p k σ).f n (MvPolynomial.monomial d a ⊗ₜ[W]
      MultivariableWeightProjection.PrimeMultivariableWeightProjection.word p k σ n v) =
        if ∀ i, p ∣ d i + (if i ∈ Set.range v then 1 else 0)
          then MvPolynomial.monomial d a ⊗ₜ[W] MultivariableWeightProjection.PrimeMultivariableWeightProjection.word p k σ n v else 0 := by
  simpa only [projection, coordinateList, Finset.mem_toList, Finset.mem_univ, forall_const] using
    MultivariableWeightProjection.PrimeMultivariableWeightProjection.successive_word p k σ (coordinateList σ) n d a v

def ordinaryProjection : DeRhamPresentationTo.DeRhamPresentation.complex W P ⟶ DeRhamPresentationTo.DeRhamPresentation.complex W P :=
  MultivariableKoszul.PrimeMultivariableKoszul.ordinaryProjection p k σ (coordinateList σ)

def ordinaryHomotopy : Homotopy (𝟙 (DeRhamPresentationTo.DeRhamPresentation.complex W P)) (ordinaryProjection p k σ) := by
  let e := OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.complexIso W σ
  simpa only [Category.id_comp, e.inv_hom_id, ordinaryProjection,
    MultivariableKoszul.PrimeMultivariableKoszul.ordinaryProjection, projection] using
    (Homotopy.refl e.inv).comp ((homotopy p k σ).comp (Homotopy.refl e.hom))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialCartierProjection.PrimePolynomialCartierProjection
