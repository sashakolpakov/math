import OAI.AlgebraicGeometry.Resolution.Blowups.TransverseCoordinatesAtPoint
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.DifferentialEquation

/-! # Transverse Hypersurface Coordinates -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TransverseHypersurfaceCoordinates.Construction

noncomputable section

/-! Boundary-preserving hypersurface coordinates from a transverse partial derivative on an étale chart. -/

variable {σ K S : Type*} [Field K] [CommRing S] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]
  [Algebra K S] [IsScalarTower K (MvPolynomial σ K) S]

theorem etaleRelativePartial_X (i j : σ) :
    DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i
      (algebraMap (MvPolynomial σ K) S (MvPolynomial.X j)) = if i = j then 1 else 0 := by
  rw [DifferentialEquation.Construction.etaleRelativePartial_algebraMap]
  by_cases hij : i = j
  · subst j
    rw [MvPolynomial.pderiv_X_self, map_one, ite_eq_left rfl]
  · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij), map_zero, ite_eq_right hij]

variable [Finite σ]

/-- A nonzero partial derivative in a direction outside the boundary
coordinates gives an actual étale neighborhood through the original point,
retaining both the hypersurface equation and every boundary equation.
The construction applies when such a transverse direction is available. -/
theorem etale_transverse_hypersurface_coordinates_at_point
    (B : Finset σ) (i : σ) (hi : i ∉ B) (z : S) (q : Ideal S) [q.IsPrime]
    (hq : DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i z ∉ q) :
    ∃ (f : DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood (DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i) z) (n : ℕ)
      (φ : MvPolynomial (Fin n ⊕ Option B) K →+* Localization.Away f)
      (η : Localization.Away f →+* q.ResidueField),
      φ.Etale ∧ (∀ r : K, φ (MvPolynomial.C r) = algebraMap K (Localization.Away f) r) ∧
      φ (MvPolynomial.X (Sum.inr none)) = algebraMap S (Localization.Away f) z ∧
      (∀ j : B, φ (MvPolynomial.X (Sum.inr (some j))) =
        algebraMap S (Localization.Away f) (algebraMap (MvPolynomial σ K) S (MvPolynomial.X j.val))) ∧
      ∀ a : S, η (algebraMap S (Localization.Away f) a) = algebraMap S q.ResidueField a := by
  let : Algebra.Smooth K (MvPolynomial σ K) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth K S := Algebra.Smooth.comp K (MvPolynomial σ K) S
  let D : B → Derivation K S S := fun j => DifferentialEquation.Construction.etaleRelativePartial (K := K) j.val
  let w : B → S := fun j => algebraMap (MvPolynomial σ K) S (MvPolynomial.X j.val)
  have hD : ∀ j k, D j (w k) = if j = k then 1 else 0 := by
    intro j k
    simpa only [Subtype.ext_iff] using etaleRelativePartial_X (K := K) (S := S) j.val k.val
  have hEw : ∀ j : B, DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i (w j) = 0 := by
    intro j
    have hij : i ≠ j.val := fun h => hi (h.symm ▸ j.property)
    simpa only [ite_eq_right hij] using etaleRelativePartial_X (K := K) (S := S) i j.val
  exact TransverseCoordinatesAtPoint.Construction.exists_boundary_preserving_transverse_coordinates_at_point
    D w (DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i) z hD hEw q hq

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TransverseHypersurfaceCoordinates.Construction
