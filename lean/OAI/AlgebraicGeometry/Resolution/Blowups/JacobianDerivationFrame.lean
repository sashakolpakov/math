import OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedEtaleFrame
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Jacobian Derivation Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.JacobianDerivationFrame.Construction

noncomputable section

/-! Dual coordinate derivations obtained by inverting a Jacobian matrix. -/

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]

def derivationJacobian (D : ι → Derivation k A A) (z : ι → A) : Matrix ι ι A :=
  fun i j => D i (z j)

/-- Normalize a derivation family by the inverse of its coordinate Jacobian. -/
def normalizedJacobianFrame (D : ι → Derivation k A A) (z : ι → A) (i : ι) : Derivation k A A :=
  ∑ j, (derivationJacobian D z)⁻¹ i j • D j

theorem normalizedJacobianFrame_apply (D : ι → Derivation k A A) (z : ι → A) (i : ι) (p : A) :
    normalizedJacobianFrame D z i p = ∑ j, (derivationJacobian D z)⁻¹ i j * D j p := by
  have h := congrArg (fun f : A → A => f p)
    (map_sum (Derivation.coeFnAddMonoidHom : Derivation k A A →+ A → A)
      (fun j => (derivationJacobian D z)⁻¹ i j • D j) Finset.univ)
  simpa only [normalizedJacobianFrame, Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply,
    Derivation.smul_apply, smul_eq_mul] using h

/-- An invertible Jacobian produces derivations exactly dual to the
chosen functions, without requiring those functions to be polynomials. -/
theorem normalizedJacobianFrame_dual (D : ι → Derivation k A A) (z : ι → A)
    (hJ : IsUnit (derivationJacobian D z).det) (i j : ι) :
    normalizedJacobianFrame D z i (z j) = if i = j then 1 else 0 := by
  rw [normalizedJacobianFrame_apply]
  change ((derivationJacobian D z)⁻¹ * derivationJacobian D z) i j = _
  rw [Matrix.nonsing_inv_mul _ hJ, Matrix.one_apply]

/-- A unit Jacobian in a smooth algebra gives actual étale neighborhoods
that preserve the entire chosen function family as polynomial coordinates. -/
theorem exists_adapted_etale_frame_of_jacobian [Algebra.Smooth k A]
    (D : ι → Derivation k A A) (z : ι → A) (hJ : IsUnit (derivationJacobian D z).det)
    (q : Ideal A) [q.IsPrime] :
    ∃ f ∉ q, ∃ (n : ℕ) (φ : MvPolynomial (Fin n ⊕ ι) k →+* Localization.Away f),
      φ.Etale ∧ (∀ r : k, φ (MvPolynomial.C r) = algebraMap k (Localization.Away f) r) ∧
      ∀ j : ι, φ (MvPolynomial.X (Sum.inr j)) = algebraMap A (Localization.Away f) (z j) :=
  AdaptedEtaleFrame.Construction.exists_adapted_etale_frame (normalizedJacobianFrame D z) z (normalizedJacobianFrame_dual D z hJ) q

end

end OAI.AlgebraicGeometry.Resolution.Blowups.JacobianDerivationFrame.Construction
