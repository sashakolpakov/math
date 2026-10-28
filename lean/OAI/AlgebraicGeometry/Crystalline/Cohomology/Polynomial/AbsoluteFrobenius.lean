import OAI.AlgebraicGeometry.Crystalline.Cohomology.RationalPolynomial

/-! # Absolute Frobenius -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius

noncomputable section

/-!
# The polynomial lift of absolute Frobenius

Combining Witt-coefficient Frobenius with x_i ↦ x_i^p reduces to
absolute Frobenius on the actual residue polynomial algebra. Its map
on the original differential symbols is the composition already used
in the completed polynomial calculation.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "φ" => WittVector.frobeniusEquiv p k

def lift : P →+* P :=
  (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.polynomialEquiv p k σ).toRingHom.comp (MvPolynomial.expand p).toRingHom

theorem lift_base (w : W) : lift p k σ (algebraMap W P w) = algebraMap W P ((φ).toRingHom w) := by
  change WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.polynomialEquiv p k σ
    (MvPolynomial.expand p (MvPolynomial.C w)) = _
  rw [MvPolynomial.expand_C]
  exact WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.polynomialEquiv_base p k σ w

theorem lift_X (i : σ) : lift p k σ (MvPolynomial.X i) = MvPolynomial.X i ^ p := by
  change MvPolynomial.map (φ).toRingHom (MvPolynomial.expand p (MvPolynomial.X i)) = _
  rw [MvPolynomial.expand_X, map_pow, MvPolynomial.map_X]

def reduction : P →+* MvPolynomial σ k := MvPolynomial.map WittVector.constantCoeff

theorem reduction_lift : (reduction p k σ).comp (lift p k σ) =
    (_root_.frobenius (MvPolynomial σ k) p).comp (reduction p k σ) := by
  apply MvPolynomial.ringHom_ext
  · intro w
    change reduction p k σ (lift p k σ (MvPolynomial.C w)) =
      _root_.frobenius (MvPolynomial σ k) p (reduction p k σ (MvPolynomial.C w))
    have hl : lift p k σ (MvPolynomial.C w) = MvPolynomial.C (φ w) := lift_base p k σ w
    rw [hl]
    change MvPolynomial.map WittVector.constantCoeff (MvPolynomial.C (φ w)) =
      _root_.frobenius (MvPolynomial σ k) p (MvPolynomial.map WittVector.constantCoeff (MvPolynomial.C w))
    rw [MvPolynomial.map_C, MvPolynomial.map_C, frobenius_def, ← map_pow]
    congr 1
    exact WittVector.coeff_frobenius_charP p w 0
  · intro i
    change reduction p k σ (lift p k σ (MvPolynomial.X i)) =
      _root_.frobenius (MvPolynomial σ k) p (reduction p k σ (MvPolynomial.X i))
    rw [lift_X, map_pow]
    rfl

def complexMap : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map (φ).toRingHom
    (DeRhamPresentationTo.DeRhamPresentation.complex W P) (DeRhamPresentationTo.DeRhamPresentation.complex W P) :=
  DeRhamSemilinearA.DeRhamSemilinearMap.complexMap W W P P (φ).toRingHom (lift p k σ) (lift_base p k σ)

theorem coefficient_symbol (n : ℕ) (a : P) (v : Fin n → P) :
    (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.complexMap p k σ).f n (DeRhamPresentationTo.DeRhamPresentation.symbol W P a v) =
      DeRhamPresentationTo.DeRhamPresentation.symbol W P (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.polynomialEquiv p k σ a)
        (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.polynomialEquiv p k σ ∘ v) :=
  DeRhamSemilinearA.DeRhamSemilinearMap.formMap_symbol W W P P (φ).toRingHom
    (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.polynomialEquiv p k σ).toRingHom
    (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.polynomialEquiv_base p k σ) n a v

theorem integral_factor (n : ℕ) (ω : DeRhamPresentationTo.DeRhamPresentation.Form W P n) :
    (complexMap p k σ).f n ω = (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.complexMap p k σ).f n
      ((Cohomology.Prime.PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap.ordinary p k σ).f n ω) := by
  have he : ((complexMap p k σ).f n).toAddMonoidHom =
      ((WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.complexMap p k σ).f n).toAddMonoidHom.comp
        ((Cohomology.Prime.PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap.ordinary p k σ).f n).hom.toAddMonoidHom := by
    apply DeRhamSemilinearA.DeRhamSemilinearMap.addHom_ext W P n
    intro a v
    change DeRhamSemilinearA.DeRhamSemilinearMap.formMap W W P P (φ).toRingHom (lift p k σ) (lift_base p k σ) n
      (DeRhamPresentationTo.DeRhamPresentation.symbol W P a v) =
        (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.complexMap p k σ).f n
          (DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (MvPolynomial.expand p)) n (DeRhamPresentationTo.DeRhamPresentation.symbol W P a v))
    rw [DeRhamSemilinearA.DeRhamSemilinearMap.formMap_symbol, DeRhamGlobalId.DeRhamGlobal.formMap_symbol, coefficient_symbol]
    rfl
  exact DFunLike.congr_fun he ω

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius
