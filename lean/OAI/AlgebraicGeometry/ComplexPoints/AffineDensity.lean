import OAI.AlgebraicGeometry.ComplexPoints.OpenIntegralMap
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Affine Density -/

namespace OAI.AlgebraicGeometry.ComplexPoints.AffineDensity.ClosednessConstruction

/-! Closedness: analytic density of principal open subsets of affine complex varieties. -/

open Set _root_.Polynomial
open scoped _root_.Topology

/-- A nonzero complex multivariate polynomial has analytically dense nonvanishing locus. -/
theorem dense_polynomial_nonzero {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (hp : p ≠ 0) :
    Dense {x : Fin n → ℂ | MvPolynomial.eval x p ≠ 0} := by
  intro x
  rw [mem_closure_iff]
  intro U hU hx
  by_contra hn
  have hzero : (fun y => MvPolynomial.eval y p) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    by_contra h
    exact hn ⟨y, hy, h⟩
  have ha : AnalyticOnNhd ℂ (fun y : Fin n → ℂ => MvPolynomial.eval y p) univ :=
    AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.id ℂ (Fin n → ℂ)) p
  have he := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ x) hzero
  apply hp
  apply MvPolynomial.funext
  intro y
  simpa using he (mem_univ y)

theorem dense_polynomial_character_nonzero {n : ℕ}
    (p : MvPolynomial (Fin n) ℂ) (hp : p ≠ 0) :
    Dense {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial (Fin n) ℂ) | x p ≠ 0} := by
  have h := (dense_polynomial_nonzero p hp).preimage
    (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph (Fin n)).isOpenMap
  change Dense {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial (Fin n) ℂ) |
    MvPolynomial.eval (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv (Fin n) x) p ≠ 0} at h
  simpa only [ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv_eval] using h

/-- For an integral nonzero element in a domain extension, the constant
coefficient of its minimal polynomial is nonzero. -/
theorem integral_minpoly_constant_ne_zero
    {R B : Type*} [CommRing R] [CommRing B] [IsDomain R] [IsDomain B]
    [Algebra R B] (b : B) (hb : IsIntegral R b) (hb0 : b ≠ 0) :
    (minpoly R b).coeff 0 ≠ 0 := by
  intro h
  have hd : minpoly R b ∣ (X : R[X]) :=
    irreducible_X.dvd_symm (minpoly.irreducible hb) (X_dvd_iff.mpr h)
  have he := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hd (minpoly.aeval R b)
  exact hb0 (by simpa using he)

/-- Every nonempty principal open in an integral finite-type complex affine
scheme is dense in the ordinary analytic topology. -/
theorem dense_affine_principal_open
    {B : Type*} [CommRing B] [Algebra ℂ B] [IsDomain B] [Algebra.FiniteType ℂ B]
    (b : B) (hb0 : b ≠ 0) : Dense {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B | x b ≠ 0} := by
  obtain ⟨n, f, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ B
  let R := MvPolynomial (Fin n) ℂ
  let : Algebra R B := f.toAlgebra
  let : IsScalarTower ℂ R B := IsScalarTower.of_algHom f
  let : Algebra.IsIntegral R B := ⟨hint⟩
  let : Module.IsTorsionFree R B :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
  have hb : IsIntegral R b := Algebra.IsIntegral.isIntegral b
  let c : R := (minpoly R b).coeff 0
  have hc : c ≠ 0 := integral_minpoly_constant_ne_zero b hb hb0
  have hbase := dense_polynomial_character_nonzero c hc
  have hopen : IsOpenMap (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f) := OpenIntegralMap.ClosednessConstruction.normal_integral_comap_isOpenMap (R := R) (B := B)
  apply (hbase.preimage hopen).mono
  intro x hx
  change Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x c ≠ 0 at hx
  intro hxb
  apply hx
  have h := congrArg x.toRingHom (minpoly.aeval R b)
  change x.toRingHom ((minpoly R b).eval₂ f.toRingHom b) = x.toRingHom 0 at h
  rw [Polynomial.hom_eval₂] at h
  change x.toRingHom b = 0 at hxb
  rw [hxb, Polynomial.eval₂_at_zero, x.toRingHom.map_zero] at h
  exact h

end OAI.AlgebraicGeometry.ComplexPoints.AffineDensity.ClosednessConstruction
