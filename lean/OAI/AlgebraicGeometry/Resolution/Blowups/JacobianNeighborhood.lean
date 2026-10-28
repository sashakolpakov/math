import OAI.AlgebraicGeometry.Resolution.Blowups.JacobianDerivationFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Derivation

/-! # Jacobian Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.JacobianNeighborhood.Construction

noncomputable section

section

/-! Actual Jacobian-open neighborhoods with adapted étale coordinates. -/

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]

abbrev derivationJacobianNeighborhood (D : ι → Derivation k A A) (z : ι → A) :=
  Localization.Away (JacobianDerivationFrame.Construction.derivationJacobian D z).det

def jacobianNeighborhoodDerivation (D : ι → Derivation k A A) (z : ι → A) (i : ι) :
    Derivation k (derivationJacobianNeighborhood D z) (derivationJacobianNeighborhood D z) :=
  letI : Algebra.FormallyEtale A (derivationJacobianNeighborhood D z) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (JacobianDerivationFrame.Construction.derivationJacobian D z).det)
  Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := derivationJacobianNeighborhood D z) (D i)

theorem jacobianNeighborhoodDerivation_constants (D : ι → Derivation k A A) (z : ι → A)
    (i : ι) (p : A) :
    jacobianNeighborhoodDerivation D z i (algebraMap A (derivationJacobianNeighborhood D z) p) =
      algebraMap A (derivationJacobianNeighborhood D z) (D i p) := by
  let : Algebra.FormallyEtale A (derivationJacobianNeighborhood D z) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (JacobianDerivationFrame.Construction.derivationJacobian D z).det)
  exact Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap (D i) p

theorem jacobianNeighborhood_jacobian_isUnit (D : ι → Derivation k A A) (z : ι → A) :
    IsUnit (JacobianDerivationFrame.Construction.derivationJacobian (jacobianNeighborhoodDerivation D z)
      (fun j => algebraMap A (derivationJacobianNeighborhood D z) (z j))).det := by
  have hM : JacobianDerivationFrame.Construction.derivationJacobian (jacobianNeighborhoodDerivation D z)
      (fun j => algebraMap A (derivationJacobianNeighborhood D z) (z j)) =
      (algebraMap A (derivationJacobianNeighborhood D z)).mapMatrix (JacobianDerivationFrame.Construction.derivationJacobian D z) := by
    funext i j
    exact jacobianNeighborhoodDerivation_constants D z i (z j)
  rw [hM, ← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (JacobianDerivationFrame.Construction.derivationJacobian D z).det

/-- Every point in the Jacobian-open neighborhood has an étale coordinate
chart retaining all the original functions, with the coefficient map unchanged. -/
theorem jacobianNeighborhood_exists_adapted_coordinates [Algebra.Smooth k A]
    (D : ι → Derivation k A A) (z : ι → A)
    (q : Ideal (derivationJacobianNeighborhood D z)) [q.IsPrime] :
    ∃ f ∉ q, ∃ (n : ℕ) (φ : MvPolynomial (Fin n ⊕ ι) k →+* Localization.Away f),
      φ.Etale ∧ (∀ r : k, φ (MvPolynomial.C r) = algebraMap k (Localization.Away f) r) ∧
      ∀ j : ι, φ (MvPolynomial.X (Sum.inr j)) = algebraMap A (Localization.Away f) (z j) := by
  let B := derivationJacobianNeighborhood D z
  let : Algebra.Smooth A B := Algebra.Smooth.of_isLocalization_Away (JacobianDerivationFrame.Construction.derivationJacobian D z).det
  let : Algebra.Smooth k B := Algebra.Smooth.comp k A B
  obtain ⟨f, hf, n, φ, hφ, hC, hX⟩ := JacobianDerivationFrame.Construction.exists_adapted_etale_frame_of_jacobian
    (jacobianNeighborhoodDerivation D z) (fun j => algebraMap A B (z j))
    (jacobianNeighborhood_jacobian_isUnit D z) q
  refine ⟨f, hf, n, φ, hφ, hC, ?_⟩
  intro j
  exact (hX j).trans (IsScalarTower.algebraMap_apply A B (Localization.Away f) (z j)).symm

end

/-! Invertible changes of individual boundary equations retain independent differentials. -/

variable {k R ι : Type*} [CommRing k] [CommRing R] [Algebra k R]
  [Fintype ι] [DecidableEq ι]

/-- At a prime containing a dual coordinate family, multiplying its
members by arbitrary units leaves a Jacobian determinant outside the prime. -/
theorem unit_boundary_jacobian_not_mem
    (z : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0)
    (u : ι → R) (hu : ∀ j, IsUnit (u j)) (q : Ideal R) [q.IsPrime]
    (hz : ∀ j, z j ∈ q) :
    (JacobianDerivationFrame.Construction.derivationJacobian D (fun j => u j * z j)).det ∉ q := by
  let φ : R →+* R ⧸ q := Ideal.Quotient.mk q
  have hmat : φ.mapMatrix (JacobianDerivationFrame.Construction.derivationJacobian D (fun j => u j * z j)) =
      Matrix.diagonal (fun j => φ (u j)) := by
    ext i j
    change φ (D i (u j * z j)) = Matrix.diagonal (fun j => φ (u j)) i j
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hD]
    have hzj : φ (z j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hz j)
    rw [hzj]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  have hunit : IsUnit (φ (JacobianDerivationFrame.Construction.derivationJacobian D (fun j => u j * z j)).det) := by
    rw [RingHom.map_det, hmat, Matrix.det_diagonal]
    exact IsUnit.prod_univ_iff.mpr (fun j => (hu j).map φ)
  intro hmem
  have hzero : φ (JacobianDerivationFrame.Construction.derivationJacobian D (fun j => u j * z j)).det = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact hunit.ne_zero hzero

end

end OAI.AlgebraicGeometry.Resolution.Blowups.JacobianNeighborhood.Construction
