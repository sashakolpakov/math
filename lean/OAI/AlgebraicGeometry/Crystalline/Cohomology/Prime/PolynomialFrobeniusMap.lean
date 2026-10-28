import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.FormFrobeniusMonomials
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamSymbol
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialSymbols
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor

/-! # Polynomial Frobenius Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap

noncomputable section

/-!
# The actual polynomial Frobenius pullback in monomial coordinates

The chain map is induced by the algebra homomorphism x_i ↦ x_i^p.
Its degree-n component is p^n times the integral weight-raising map.
The coefficient Witt Frobenius is kept separate from this W-linear map.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [Fintype σ]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomialComplex W σ
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.complexIso W σ

def ordinary : DeRhamPresentationTo.DeRhamPresentation.complex W P ⟶ DeRhamPresentationTo.DeRhamPresentation.complex W P :=
  NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map (CommAlgCat.ofHom (MvPolynomial.expand p))

def map : K ⟶ K := (E).hom ≫ ordinary p k σ ≫ (E).inv

theorem map_hom : map p k σ ≫ (E).hom = (E).hom ≫ ordinary p k σ := by
  simp only [map, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem hom_map_apply (n : ℕ) (x : (K).X n) :
    (E).hom.f n ((map p k σ).f n x) = (ordinary p k σ).f n ((E).hom.f n x) := by
  exact ConcreteCategory.congr_hom (congrArg (fun f : K ⟶ DeRhamPresentationTo.DeRhamPresentation.complex W P => f.f n)
    (map_hom p k σ)) x

omit [Fintype σ] in
theorem symbol_monomial_smul (n : ℕ) (d : σ →₀ ℕ) (r : W) (v : Fin n → P) :
    DeRhamPresentationTo.DeRhamPresentation.symbol W P (MvPolynomial.monomial d r) v =
      r • DeRhamPresentationTo.DeRhamPresentation.symbol W P (MvPolynomial.monomial d 1) v := by
  change (DeRhamPresentationTo.DeRhamPresentation.relations W P n).mkQ (Finsupp.single v (MvPolynomial.monomial d r)) =
    r • (DeRhamPresentationTo.DeRhamPresentation.relations W P n).mkQ (Finsupp.single v (MvPolynomial.monomial d 1))
  rw [← (DeRhamPresentationTo.DeRhamPresentation.relations W P n).mkQ.map_smul_of_tower r]
  congr 1
  rw [Finsupp.smul_single, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

variable [LinearOrder σ]

theorem hom_basis (n : ℕ) (d : σ →₀ ℕ) (s : Set.powersetCard σ n) :
    (E).hom.f n (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s)) =
      DeRhamPresentationTo.DeRhamPresentation.symbol W P (MvPolynomial.monomial d 1)
        (MvPolynomial.X ∘ Set.powersetCard.ofFinEmbEquiv.symm s) := by
  let f : Koszul.Tensor.KoszulTensor.Term W σ P n →ₗ[W] DeRhamPresentationTo.DeRhamPresentation.Form W P n := ((E).hom.f n).hom
  exact (congrArg f (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis_apply W σ n d s)).trans
    (OrdinaryPolynomialSymbols.OrdinaryPolynomialCoordinateSymbols.hom_word W σ n (MvPolynomial.monomial d 1)
      (Set.powersetCard.ofFinEmbEquiv.symm s))

theorem ordinary_basis_symbol (n : ℕ) (d : σ →₀ ℕ) (s : Set.powersetCard σ n) :
    (ordinary p k σ).f n
      (DeRhamPresentationTo.DeRhamPresentation.symbol W P (MvPolynomial.monomial d 1)
        (MvPolynomial.X ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) =
      DeRhamPresentationTo.DeRhamPresentation.symbol W P
        (MvPolynomial.monomial (FormFrobeniusWeights.PrimeFormFrobeniusWeights.raiseExponent p σ s d) ((p : W) ^ n))
        (MvPolynomial.X ∘ Set.powersetCard.ofFinEmbEquiv.symm s) := by
  change DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (MvPolynomial.expand p)) n _ = _
  rw [DeRhamGlobalId.DeRhamGlobal.formMap_symbol]
  change DeRhamPresentationTo.DeRhamPresentation.symbol W P (MvPolynomial.expand p (MvPolynomial.monomial d 1))
    (fun j => MvPolynomial.expand p (MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s j))) = _
  simp only [MvPolynomial.expand_X]
  rw [DeRhamSymbol.DeRhamSymbolPowers.symbol_powers, FormFrobeniusMonomials.PrimeFormFrobeniusMonomials.pullback_coefficient]
  rfl

theorem map_basis (n : ℕ) (d : σ →₀ ℕ) (s : Set.powersetCard σ n) :
    (map p k σ).f n (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s)) =
      (p : W) ^ n • Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n
        (FormFrobeniusWeights.PrimeFormFrobeniusWeights.raiseExponent p σ s d, s) := by
  let e : Koszul.Tensor.KoszulTensor.Term W σ P n →ₗ[W] DeRhamPresentationTo.DeRhamPresentation.Form W P n := ((E).hom.f n).hom
  let f : Module.End W (Koszul.Tensor.KoszulTensor.Term W σ P n) := ((map p k σ).f n).hom
  let o : Module.End W (DeRhamPresentationTo.DeRhamPresentation.Form W P n) := ((ordinary p k σ).f n).hom
  have he : Function.Injective e := (ModuleCat.mono_iff_injective ((E).hom.f n)).mp inferInstance
  change f (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s)) = _
  apply he
  calc
    _ = o (e (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s))) :=
      by exact hom_map_apply p k σ n _
    _ = o (DeRhamPresentationTo.DeRhamPresentation.symbol W P (MvPolynomial.monomial d 1)
        (MvPolynomial.X ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) :=
      by exact congrArg o (hom_basis p k σ n d s)
    _ = DeRhamPresentationTo.DeRhamPresentation.symbol W P
        (MvPolynomial.monomial (FormFrobeniusWeights.PrimeFormFrobeniusWeights.raiseExponent p σ s d) ((p : W) ^ n))
        (MvPolynomial.X ∘ Set.powersetCard.ofFinEmbEquiv.symm s) :=
      by exact ordinary_basis_symbol p k σ n d s
    _ = (p : W) ^ n • DeRhamPresentationTo.DeRhamPresentation.symbol W P
        (MvPolynomial.monomial (FormFrobeniusWeights.PrimeFormFrobeniusWeights.raiseExponent p σ s d) 1)
        (MvPolynomial.X ∘ Set.powersetCard.ofFinEmbEquiv.symm s) :=
      by exact symbol_monomial_smul p k σ n _ _ _
    _ = (p : W) ^ n • e (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n
        (FormFrobeniusWeights.PrimeFormFrobeniusWeights.raiseExponent p σ s d, s)) :=
      by exact congrArg ((p : W) ^ n • ·) (hom_basis p k σ n _ s).symm
    _ = _ := (e.map_smul ((p : W) ^ n) _).symm

theorem map_f (n : ℕ) :
    (show Module.End W (Koszul.Tensor.KoszulTensor.Term W σ P n) from ((map p k σ).f n).hom) =
    (p : W) ^ n • FormFrobeniusWeights.PrimeFormFrobeniusWeights.raise p k σ n := by
  apply (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n).ext
  rintro ⟨d, s⟩
  change (map p k σ).f n (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s)) = _
  exact (map_basis p k σ n d s).trans
    (congrArg ((p : W) ^ n • ·) (FormFrobeniusWeights.PrimeFormFrobeniusWeights.raise_basis p k σ n d s)).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap
