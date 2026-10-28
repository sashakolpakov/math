import OAI.ArithmeticGeometry.Models.SpreadingOut.PolynomialCoordinates

/-! # Root Scalar Extension -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.RootScalarExtension.Construction

noncomputable section

/-! Scalar extension of a root algebra, with its coefficient inclusion tracked. -/

open scoped TensorProduct

universe u

@[simp]
theorem polynomialHypersurfaceIso_symm_mk
    (R : Type u) [CommRing R] (n : ℕ) (p q : Polynomial (MvPolynomial (Fin n) R)) :
    (PolynomialCoordinates.Construction.polynomialHypersurfaceIso R n p).symm (AdjoinRoot.mk p q) =
      Ideal.Quotient.mk _ ((MvPolynomial.finSuccEquiv R n).symm q) := by
  apply (PolynomialCoordinates.Construction.polynomialHypersurfaceIso R n p).injective
  rw [AlgEquiv.apply_symm_apply, PolynomialCoordinates.Construction.polynomialHypersurfaceIso_mk, AlgEquiv.apply_symm_apply]

def rootScalarExtensionIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) R)) :
    S ⊗[R] AdjoinRoot p ≃ₐ[S]
      AdjoinRoot (Polynomial.map (MvPolynomial.map (algebraMap R S)) p) := by
  let e₁ := Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
    (PolynomialCoordinates.Construction.polynomialHypersurfaceIso R n p).symm
  let e₂ := HypersurfaceScalarExtension.Construction.hypersurfaceScalarExtensionIso R S ((MvPolynomial.finSuccEquiv R n).symm p)
  let e₃ := Ideal.quotientEquivAlgOfEq S
    (congrArg (fun q : MvPolynomial (Fin (n + 1)) S ↦ Ideal.span ({q} : Set _))
      (PolynomialCoordinates.Construction.map_finSuccEquiv_symm (algebraMap R S) n p))
  exact e₁.trans (e₂.trans (e₃.trans (PolynomialCoordinates.Construction.polynomialHypersurfaceIso S n _)))

@[simp]
theorem rootScalarExtensionIso_one_tmul_mk
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (p q : Polynomial (MvPolynomial (Fin n) R)) :
    rootScalarExtensionIso R S n p (1 ⊗ₜ[R] AdjoinRoot.mk p q) =
      AdjoinRoot.mk _ (Polynomial.map (MvPolynomial.map (algebraMap R S)) q) := by
  simp only [rootScalarExtensionIso, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_one, AlgEquiv.coe_toAlgHom, polynomialHypersurfaceIso_symm_mk,
    PolynomialCoordinates.Construction.hypersurfaceScalarExtensionIso_tmul_mk, one_smul, Ideal.quotientEquivAlgOfEq_mk,
    PolynomialCoordinates.Construction.polynomialHypersurfaceIso_mk, PolynomialCoordinates.Construction.finSuccEquiv_map, AlgEquiv.apply_symm_apply]

@[simp]
theorem rootScalarExtensionIso_one_tmul_algebraMap
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) R)) (d : MvPolynomial (Fin n) R) :
    rootScalarExtensionIso R S n p (1 ⊗ₜ[R] algebraMap _ (AdjoinRoot p) d) =
      algebraMap _ (AdjoinRoot (Polynomial.map (MvPolynomial.map (algebraMap R S)) p))
        (MvPolynomial.map (algebraMap R S) d) := by
  change rootScalarExtensionIso R S n p (1 ⊗ₜ[R] AdjoinRoot.mk p (Polynomial.C d)) = _
  rw [rootScalarExtensionIso_one_tmul_mk, Polynomial.map_C]
  rfl

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.RootScalarExtension.Construction
