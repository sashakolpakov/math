import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.CoefficientPolynomials
import OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousPolynomialScaling

/-! # Normalized Homogeneous Polynomials -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NormalizedHomogeneousPolynomials.Dolbeault

noncomputable section

section

/-! Homogeneous polynomials with prescribed coordinate-hyperplane zeros. -/

open _root_.TopologicalSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def normalizedHomogeneousPolynomials (J : Finset ι) (k : ℕ) : Submodule ℂ (MvPolynomial ι ℂ) where
  carrier := {P | P.IsHomogeneous k ∧
    ∀ i ∈ J, ∀ x : ι → ℂ, x i = 0 → MvPolynomial.eval x P = 0}
  zero_mem' := ⟨MvPolynomial.isHomogeneous_zero ι ℂ k, fun _ _ _ _ => map_zero _⟩
  add_mem' := by
    intro P Q hP hQ
    refine ⟨hP.1.add hQ.1, ?_⟩
    intro i hi x hx
    rw [map_add, hP.2 i hi x hx, hQ.2 i hi x hx, add_zero]
  smul_mem' := by
    intro c P hP
    refine ⟨(MvPolynomial.homogeneousSubmodule ι ℂ k).smul_mem c hP.1, ?_⟩
    intro i hi x hx
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, hP.2 i hi x hx, mul_zero]

def negativePolynomialCoefficient (N k : ℕ)
    (P : normalizedHomogeneousPolynomials (Finset.univ : Finset (Fin N)) k) :
    HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin N)) (-(k : ℤ)) := by
  refine ⟨PolynomialHolomorphicSections.AnalyticLocal.polynomialCoefficientSection P.val ⊤, ?_, ?_⟩
  · intro i hi x hx
    exact P.property.2 i hi x.val hx
  · intro c hc x
    have hpoint : Laurent.FiniteUniqueness.Dolbeault.laurentSectorScale c (Finset.univ : Finset (Fin N)) x = c⁻¹ • x := by
      funext i
      simp only [Laurent.FiniteUniqueness.Dolbeault.laurentSectorScale, Finset.mem_univ, ite_true, Pi.smul_apply, smul_eq_mul]
    change MvPolynomial.eval (Laurent.FiniteUniqueness.Dolbeault.laurentSectorScale c Finset.univ x) P.val =
      c ^ (-(k : ℤ)) * MvPolynomial.eval x P.val
    rw [hpoint, HomogeneousPolynomialScaling.Dolbeault.homogeneousPolynomial_eval_smul P.val k P.property.1, zpow_neg, zpow_natCast, inv_pow]

theorem negativePolynomialCoefficient_apply (N k : ℕ)
    (P : normalizedHomogeneousPolynomials (Finset.univ : Finset (Fin N)) k) (x : Fin N → ℂ) :
    Laurent.SectorSum.Dolbeault.laurentEntireFunction (negativePolynomialCoefficient N k P).val x = MvPolynomial.eval x P.val := rfl

def negativePolynomialCoefficientMap (N k : ℕ) :
    normalizedHomogeneousPolynomials (Finset.univ : Finset (Fin N)) k →ₗ[ℂ]
      HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin N)) (-(k : ℤ)) where
  toFun := negativePolynomialCoefficient N k
  map_add' P Q := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact map_add (MvPolynomial.eval x.val) P.val Q.val
  map_smul' c P := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change MvPolynomial.eval x.val (c • P.val) = c * MvPolynomial.eval x.val P.val
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]

end

/-! All-positive entire coefficients of nonnegative degree are homogeneous polynomials. -/

open _root_.TopologicalSpace

def positivePolynomialCoefficient (N k : ℕ) (P : MvPolynomial.homogeneousSubmodule (Fin N) ℂ k) :
    HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin N)) (k : ℤ) := by
  refine ⟨PolynomialHolomorphicSections.AnalyticLocal.polynomialCoefficientSection P.val ⊤, ?_, ?_⟩
  · intro i hi
    exact (Finset.notMem_empty i hi).elim
  · intro c hc x
    have hpoint : Laurent.FiniteUniqueness.Dolbeault.laurentSectorScale c (∅ : Finset (Fin N)) x = c • x := by
      funext i
      simp only [Laurent.FiniteUniqueness.Dolbeault.laurentSectorScale, Finset.notMem_empty, ite_false, Pi.smul_apply, smul_eq_mul]
    change MvPolynomial.eval (Laurent.FiniteUniqueness.Dolbeault.laurentSectorScale c ∅ x) P.val = c ^ (k : ℤ) * MvPolynomial.eval x P.val
    rw [hpoint, HomogeneousPolynomialScaling.Dolbeault.homogeneousPolynomial_eval_smul P.val k P.property, zpow_natCast]

def positivePolynomialCoefficientMap (N k : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin N) ℂ k →ₗ[ℂ]
      HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin N)) (k : ℤ) where
  toFun := positivePolynomialCoefficient N k
  map_add' P Q := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact map_add (MvPolynomial.eval x.val) P.val Q.val
  map_smul' c P := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact MvPolynomial.smul_eval x.val P.val c

theorem positivePolynomialCoefficientMap_injective (N k : ℕ) :
    Function.Injective (positivePolynomialCoefficientMap N k) := by
  intro P Q h
  apply Subtype.ext
  apply P.property.funext Q.property
  intro x
  exact congrArg (fun a : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin N)) (k : ℤ) =>
    Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val x) h

theorem positivePolynomialCoefficientMap_surjective (N k : ℕ) :
    Function.Surjective (positivePolynomialCoefficientMap N k) := by
  intro a
  obtain ⟨P, hP, he⟩ := Laurent.CoefficientPolynomials.Dolbeault.positiveCoefficient_exists_polynomial k a
  refine ⟨⟨P, hP⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact he x.val

def positivePolynomialCoefficientEquiv (N k : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin N) ℂ k ≃ₗ[ℂ]
      HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin N)) (k : ℤ) :=
  LinearEquiv.ofBijective (positivePolynomialCoefficientMap N k)
    ⟨positivePolynomialCoefficientMap_injective N k, positivePolynomialCoefficientMap_surjective N k⟩

theorem positivePolynomialCoefficientEquiv_apply (N k : ℕ)
    (P : MvPolynomial.homogeneousSubmodule (Fin N) ℂ k) (x : Fin N → ℂ) :
    Laurent.SectorSum.Dolbeault.laurentEntireFunction (positivePolynomialCoefficientEquiv N k P).val x = MvPolynomial.eval x P.val := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.NormalizedHomogeneousPolynomials.Dolbeault
