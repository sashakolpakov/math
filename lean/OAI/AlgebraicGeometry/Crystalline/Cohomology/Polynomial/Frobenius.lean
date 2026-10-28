import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialTransferInversion
import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionLinear
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension

/-! # Frobenius -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Frobenius.PolynomialFrobenius

noncomputable section

/-!
# Frobenius on the p-adically completed polynomial de Rham complex

Complete the integral polynomial form modules first, then extend their
scalars to the original Witt-vector fraction field. The explicit bounded
integral transfer gives a homotopy inverse to polynomial substitution.
No exactness of completion or interchange with rationalization is used.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [Fintype σ]

local notation "W" => WittVector p k
local notation "K₀" => FractionRing W
local notation "P" => MvPolynomial σ W

def coefficients : ModuleCat.{u} W ⥤ ModuleCat.{u} K₀ :=
  NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionLinear.functor (Ideal.span {(p : W)}) ⋙
    IntrinsicScalarExtension.functor W K₀

instance coefficients_additive : (coefficients p k).Additive := by
  unfold coefficients
  infer_instance

abbrev complex : CochainComplex (ModuleCat.{u} K₀) ℕ :=
  Cohomology.Prime.PolynomialTransferInversion.PrimePolynomialTransferInversion.complex p k σ K₀ (coefficients p k)

def frobenius : complex p k σ ⟶ complex p k σ :=
  Cohomology.Prime.PolynomialTransferInversion.PrimePolynomialTransferInversion.frobenius p k σ K₀ (coefficients p k)

def homotopyEquiv : HomotopyEquiv (complex p k σ) (complex p k σ) := by
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact Cohomology.Prime.PolynomialTransferInversion.PrimePolynomialTransferInversion.homotopyEquiv p k σ K₀ (coefficients p k)

instance frobenius_quasiIso : QuasiIso (frobenius p k σ) :=
  HomotopyEquiv.quasiIso_hom (homotopyEquiv p k σ)

abbrev ordinaryComplex : CochainComplex (ModuleCat.{u} K₀) ℕ :=
  ((coefficients p k).mapHomologicalComplex (.up ℕ)).obj (DeRhamPresentationTo.DeRhamPresentation.complex W P)

def ordinaryFrobenius : ordinaryComplex p k σ ⟶ ordinaryComplex p k σ :=
  ((coefficients p k).mapHomologicalComplex (.up ℕ)).map (Cohomology.Prime.PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap.ordinary p k σ)

def coordinateIso : complex p k σ ≅ ordinaryComplex p k σ :=
  ((coefficients p k).mapHomologicalComplex (.up ℕ)).mapIso (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.complexIso W σ)

theorem coordinate_frobenius : frobenius p k σ =
    (coordinateIso p k σ).hom ≫ ordinaryFrobenius p k σ ≫ (coordinateIso p k σ).inv := by
  change ((coefficients p k).mapHomologicalComplex (.up ℕ)).map
    (Cohomology.Prime.PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap.map p k σ) = _
  rw [Cohomology.Prime.PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap.map, Functor.map_comp, Functor.map_comp]
  rfl

instance ordinaryFrobenius_quasiIso : QuasiIso (ordinaryFrobenius p k σ) := by
  have h : QuasiIso ((coordinateIso p k σ).hom ≫ ordinaryFrobenius p k σ ≫
      (coordinateIso p k σ).inv) := by
    rw [← coordinate_frobenius]
    infer_instance
  let := h
  have h' : QuasiIso (ordinaryFrobenius p k σ ≫ (coordinateIso p k σ).inv) :=
    quasiIso_of_comp_left (coordinateIso p k σ).hom _
  let := h'
  exact quasiIso_of_comp_right _ (coordinateIso p k σ).inv

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Frobenius.PolynomialFrobenius
