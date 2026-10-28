import OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedEtaleFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.NeighborhoodCoefficientOrder

/-! # Transverse Coordinates At Point -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TransverseCoordinatesAtPoint.Construction

noncomputable section

section

/-! Transverse hypersurface coordinates on the actual derivative open, with the old boundary retained. -/

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- Normalizing a derivative on its actual invertibility open retains
every equation that the derivative annihilated. -/
theorem normalizedNeighborhoodDerivation_zero (E : Derivation k A A) (z w : A)
    (hw : E w = 0) :
    NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation E z (algebraMap A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood E z) w) = 0 := by
  let : Algebra.FormallyEtale A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood E z) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (E z))
  unfold NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation
  rw [Derivation.smul_apply, Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hw, map_zero, smul_zero]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Algebra.Smooth k A]

/-- If a derivative is transverse to a hypersurface and annihilates the
existing boundary equations, its actual derivative open has further étale
coordinates preserving all of those original equations simultaneously. -/
theorem derivativeNeighborhood_exists_boundary_preserving_coordinates
    (D : ι → Derivation k A A) (w : ι → A) (E : Derivation k A A) (z : A)
    (hD : ∀ i j, D i (w j) = if i = j then 1 else 0) (hEw : ∀ i, E (w i) = 0)
    (q : Ideal (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood E z)) [q.IsPrime] :
    ∃ f ∉ q, ∃ (n : ℕ) (φ : MvPolynomial (Fin n ⊕ Option ι) k →+* Localization.Away f),
      φ.Etale ∧ (∀ r : k, φ (MvPolynomial.C r) = algebraMap k (Localization.Away f) r) ∧
      φ (MvPolynomial.X (Sum.inr none)) = algebraMap A (Localization.Away f) z ∧
      ∀ i, φ (MvPolynomial.X (Sum.inr (some i))) = algebraMap A (Localization.Away f) (w i) := by
  let B := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood E z
  let : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (E z))
  let : Algebra.Smooth A B := Algebra.Smooth.of_isLocalization_Away (E z)
  let : Algebra.Smooth k B := Algebra.Smooth.comp k A B
  let D' : ι → Derivation k B B := fun i => Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := B) (D i)
  let w' : ι → B := fun i => algebraMap A B (w i)
  have hD' : ∀ i j, D' i (w' j) = if i = j then 1 else 0 := by
    intro i j
    change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := B) (D i) (algebraMap A B (w j)) = _
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hD]
    split_ifs <;> simp
  obtain ⟨f, hf, n, φ, hφ, hC, hZ, hW⟩ := AdaptedEtaleFrame.Construction.exists_adapted_transverse_coordinates
    D' w' (NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation E z) (algebraMap A B z) hD'
    (NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation_equation E z)
    (fun i => normalizedNeighborhoodDerivation_zero E z (w i) (hEw i)) q
  refine ⟨f, hf, n, φ, hφ, hC, ?_, ?_⟩
  · exact hZ.trans (IsScalarTower.algebraMap_apply A B (Localization.Away f) z).symm
  · intro i
    exact (hW i).trans (IsScalarTower.algebraMap_apply A B (Localization.Away f) (w i)).symm

end

/-! Boundary-preserving transverse coordinates with an explicit lift of the original point. -/

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [Fintype ι] [DecidableEq ι] [Algebra.Smooth k A]

/-- A nonzero transverse derivative at the original prime gives an actual
étale localization through that same point. Every old boundary equation and
the chosen hypersurface equation are retained, and a residue-field map
verifies the point and all original affine functions. -/
theorem exists_boundary_preserving_transverse_coordinates_at_point
    (D : ι → Derivation k A A) (w : ι → A) (E : Derivation k A A) (z : A)
    (hD : ∀ i j, D i (w j) = if i = j then 1 else 0) (hEw : ∀ i, E (w i) = 0)
    (q : Ideal A) [q.IsPrime] (hq : E z ∉ q) :
    ∃ (f : DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood E z) (n : ℕ)
      (φ : MvPolynomial (Fin n ⊕ Option ι) k →+* Localization.Away f)
      (η : Localization.Away f →+* q.ResidueField),
      φ.Etale ∧ (∀ r : k, φ (MvPolynomial.C r) = algebraMap k (Localization.Away f) r) ∧
      φ (MvPolynomial.X (Sum.inr none)) = algebraMap A (Localization.Away f) z ∧
      (∀ i, φ (MvPolynomial.X (Sum.inr (some i))) = algebraMap A (Localization.Away f) (w i)) ∧
      ∀ a : A, η (algebraMap A (Localization.Away f) a) = algebraMap A q.ResidueField a := by
  let B := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood E z
  have hEz : algebraMap A q.ResidueField (E z) ≠ 0 :=
    fun h => hq (Ideal.algebraMap_residueField_eq_zero.mp h)
  let e : B →+* q.ResidueField :=
    IsLocalization.Away.lift (g := algebraMap A q.ResidueField) (E z) (isUnit_iff_ne_zero.mpr hEz)
  let Q := RingHom.ker e
  let : Q.IsPrime := RingHom.ker_isPrime e
  obtain ⟨f, hf, n, φ, hφ, hC, hZ, hW⟩ :=
    derivativeNeighborhood_exists_boundary_preserving_coordinates D w E z hD hEw Q
  have hef : e f ≠ 0 := hf
  let η : Localization.Away f →+* q.ResidueField :=
    IsLocalization.Away.lift (g := e) f (isUnit_iff_ne_zero.mpr hef)
  refine ⟨f, n, φ, η, hφ, hC, hZ, hW, ?_⟩
  intro a
  rw [IsScalarTower.algebraMap_apply A B (Localization.Away f)]
  change IsLocalization.Away.lift (g := e) f (isUnit_iff_ne_zero.mpr hef)
    (algebraMap B (Localization.Away f) (algebraMap A B a)) = _
  rw [IsLocalization.Away.lift_eq]
  exact IsLocalization.Away.lift_eq _ _ _

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TransverseCoordinatesAtPoint.Construction
