import OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceScalarExtension
import Mathlib.RingTheory.AdjoinRoot

/-! # Polynomial Coordinates -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.PolynomialCoordinates.Construction

noncomputable section

/-! Compatibility of the multivariate and monic-polynomial presentations of
an affine hypersurface. -/

open scoped TensorProduct

universe u

theorem finSuccEquiv_map
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.finSuccEquiv S n (MvPolynomial.map φ p) =
      Polynomial.map (MvPolynomial.map φ) (MvPolynomial.finSuccEquiv R n p) := by
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro m
  simp only [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_map,
    Polynomial.coeff_map]

theorem map_finSuccEquiv_symm
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ)
    (p : Polynomial (MvPolynomial (Fin n) R)) :
    MvPolynomial.map φ ((MvPolynomial.finSuccEquiv R n).symm p) =
      (MvPolynomial.finSuccEquiv S n).symm (Polynomial.map (MvPolynomial.map φ) p) := by
  apply (MvPolynomial.finSuccEquiv S n).injective
  rw [finSuccEquiv_map, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

def polynomialHypersurfaceIso
    (R : Type u) [CommRing R] (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) R)) :
    (MvPolynomial (Fin (n + 1)) R ⧸ Ideal.span
      ({(MvPolynomial.finSuccEquiv R n).symm p} : Set _)) ≃ₐ[R] AdjoinRoot p := by
  apply Ideal.quotientEquivAlg _ _ (MvPolynomial.finSuccEquiv R n)
  rw [Ideal.map_span, Set.image_singleton]
  congr 1
  apply congrArg Set.singleton
  exact ((MvPolynomial.finSuccEquiv R n).apply_symm_apply _).symm

@[simp]
theorem polynomialHypersurfaceIso_mk
    (R : Type u) [CommRing R] (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) R))
    (q : MvPolynomial (Fin (n + 1)) R) :
    polynomialHypersurfaceIso R n p (Ideal.Quotient.mk _ q) =
      AdjoinRoot.mk p (MvPolynomial.finSuccEquiv R n q) := rfl

@[simp]
theorem hypersurfaceScalarExtensionIso_tmul_mk
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {σ : Type*} (p q : MvPolynomial σ R) (s : S) :
    HypersurfaceScalarExtension.Construction.hypersurfaceScalarExtensionIso R S p (s ⊗ₜ[R] Ideal.Quotient.mk _ q) =
      Ideal.Quotient.mk _ (s • MvPolynomial.map (algebraMap R S) q) := by
  simp only [HypersurfaceScalarExtension.Construction.hypersurfaceScalarExtensionIso, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk, MvPolynomial.algebraTensorAlgEquiv_tmul]

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.PolynomialCoordinates.Construction
