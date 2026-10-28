import OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentResidueNaturality

/-! # Laurent Polynomial Action -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentPolynomialAction

noncomputable section

/-! Homogeneous polynomial multiplication on the actual allowed Laurent
modules of the projective coordinate intersections. The maps commute
with enlarging an intersection and agree with ambient Laurent multiplication. -/

open _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentResiduePairing

universe u

variable {σ : Type} [Fintype σ] (C : Type u) [CommRing C]

abbrev Allowed (d : ℤ) {n : ℕ} (a : Fin (n + 1) → σ) :=
  {e : AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d // e.IsAllowedOn a}

def shift (m : ℕ) (d : ℤ) {n : ℕ} (a : Fin (n + 1) → σ)
    (e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ)) (f : Allowed d a) :
    Allowed ((m : ℤ) + d) a :=
  ⟨⟨e.val.val + f.val.val, by
      rw [map_add, e.val.property, f.val.property]⟩, by
    intro i hi
    apply f.property
    have he := e.property i
    change e.val.val i + f.val.val i < 0 at hi
    change f.val.val i < 0
    omega⟩

def monomial (m : ℕ) (d : ℤ) {n : ℕ} (a : Fin (n + 1) → σ)
    (e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ)) :
    AddMonoidAlgebra C (Allowed d a) →ₗ[C]
      AddMonoidAlgebra C (Allowed ((m : ℤ) + d) a) :=
  AddMonoidAlgebra.mapDomainLinearMap C C (shift m d a e)

def polynomial (m : ℕ) (d : ℤ) {n : ℕ} (a : Fin (n + 1) → σ)
    (P : homogeneousSubmodule σ C m) :
    AddMonoidAlgebra C (Allowed d a) →ₗ[C]
      AddMonoidAlgebra C (Allowed ((m : ℤ) + d) a) :=
  ∑ e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ),
    AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv C m P e • monomial C m d a e

def ambient (d : ℤ) {n : ℕ} (a : Fin (n + 1) → σ) :
    AddMonoidAlgebra C (Allowed d a) →ₗ[C] AddMonoidAlgebra C (σ →₀ ℤ) :=
  AddMonoidAlgebra.mapDomainLinearMap C C (fun e => e.val.val)

omit [Fintype σ] in
theorem ambient_injective (d : ℤ) {n : ℕ} (a : Fin (n + 1) → σ) :
    Function.Injective (ambient C d a) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro e f h
  exact Subtype.ext (Subtype.ext h)

omit [Fintype σ] in
theorem ambient_monomial (m : ℕ) (d : ℤ) {n : ℕ} (a : Fin (n + 1) → σ)
    (e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ)) (x : AddMonoidAlgebra C (Allowed d a)) :
    ambient C ((m : ℤ) + d) a (monomial C m d a e x) =
      AddMonoidAlgebra.single e.val.val 1 * ambient C d a x := by
  have h : (ambient C ((m : ℤ) + d) a).comp (monomial C m d a e) =
      (LinearMap.mulLeft C (AddMonoidAlgebra.single e.val.val 1)).comp (ambient C d a) := by
    apply AddMonoidAlgebra.lhom_ext'
    intro f
    apply LinearMap.ext
    intro c
    simp only [LinearMap.comp_apply, AddMonoidAlgebra.lsingle_apply,
      ambient, monomial, AddMonoidAlgebra.mapDomainLinearMap_single,
      LinearMap.mulLeft_apply, AddMonoidAlgebra.single_mul_single, one_mul]
    rfl
  exact LinearMap.congr_fun h x

theorem ambient_polynomial (m : ℕ) (d : ℤ) {n : ℕ} (a : Fin (n + 1) → σ)
    (P : homogeneousSubmodule σ C m) (x : AddMonoidAlgebra C (Allowed d a)) :
    ambient C ((m : ℤ) + d) a (polynomial C m d a P x) =
      LaurentResiduePairing.polynomialMap σ C P.val * ambient C d a x := by
  classical
  simp only [polynomial, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, ambient_monomial, LaurentResiduePairing.polynomialMap_homogeneous, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [← smul_mul_assoc, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

def enlarge (d : ℤ) {n k : ℕ} (a : Fin (n + 1) → σ) (b : Fin (k + 1) → σ)
    (h : Set.range a ⊆ Set.range b) : Allowed d a → Allowed d b :=
  fun e => ⟨e.val, fun _ hi => h (e.property hi)⟩

def restriction (d : ℤ) {n k : ℕ} (a : Fin (n + 1) → σ) (b : Fin (k + 1) → σ)
    (h : Set.range a ⊆ Set.range b) :
    AddMonoidAlgebra C (Allowed d a) →ₗ[C] AddMonoidAlgebra C (Allowed d b) :=
  AddMonoidAlgebra.mapDomainLinearMap C C (enlarge d a b h)

omit [Fintype σ] in
theorem ambient_restriction (d : ℤ) {n k : ℕ} (a : Fin (n + 1) → σ)
    (b : Fin (k + 1) → σ) (h : Set.range a ⊆ Set.range b)
    (x : AddMonoidAlgebra C (Allowed d a)) :
    ambient C d b (restriction C d a b h x) = ambient C d a x := by
  have heq : (ambient C d b).comp (restriction C d a b h) = ambient C d a := by
    rw [ambient, restriction, ← AddMonoidAlgebra.mapDomainLinearMap_comp]
    rfl
  exact LinearMap.congr_fun heq x

theorem polynomial_restriction (m : ℕ) (d : ℤ) {n k : ℕ}
    (a : Fin (n + 1) → σ) (b : Fin (k + 1) → σ)
    (h : Set.range a ⊆ Set.range b) (P : homogeneousSubmodule σ C m)
    (x : AddMonoidAlgebra C (Allowed d a)) :
    restriction C ((m : ℤ) + d) a b h (polynomial C m d a P x) =
      polynomial C m d b P (restriction C d a b h x) := by
  apply ambient_injective C ((m : ℤ) + d) b
  rw [ambient_restriction, ambient_polynomial, ambient_polynomial, ambient_restriction]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentPolynomialAction
