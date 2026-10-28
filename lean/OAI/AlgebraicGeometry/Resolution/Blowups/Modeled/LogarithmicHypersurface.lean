import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.AtPrime
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicTransverseEquation

/-! # Logarithmic Hypersurface -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.LogarithmicHypersurface.Construction

noncomputable section

/-! Actual transverse hypersurface neighborhoods for boundary equations given by a local model. -/

universe u v

variable {k A : Type u} {ι : Type v} [Field k]
  [CommRing A] [Algebra k A] {w : ι → A}

/-- The logarithmic bound supplies an actual hypersurface neighborhood
for unit-scaled boundary equations at any prime. The relative argument
requires no restriction on the field's characteristic. The original field, point, normal
equation, and each finite model boundary coordinate are all retained. -/
theorem exists_modeled_logarithmic_hypersurface
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k A ι w) (q : Ideal A) [q.IsPrime]
    (hw : ∀ j, w j ∈ q) (J : Ideal A) (n : ℕ)
    (hJ : J.map (algebraMap A (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (n + 1))
    (hbound : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J (n + 1) = ⊤) :
    ∃ (z : A) (E : Derivation k A A)
      (f : DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood E z) (d : ℕ)
      (φ : MvPolynomial (Fin d ⊕ Option M.boundaryIndices) k →+* Localization.Away f)
      (η : Localization.Away f →+* q.ResidueField),
      z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ∧ z ∈ q ∧ E z ∉ q ∧
      E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w ∧ φ.Etale ∧
      (∀ c : k, φ (MvPolynomial.C c) = algebraMap k (Localization.Away f) c) ∧
      φ (MvPolynomial.X (Sum.inr none)) = algebraMap A (Localization.Away f) z ∧
      (∀ s : M.boundaryIndices, φ (MvPolynomial.X (Sum.inr (some s))) =
        algebraMap A (Localization.Away f) (M.map (MvPolynomial.X s.val))) ∧
      ∀ r : A, η (algebraMap A (Localization.Away f) r) = algebraMap A q.ResidueField r := by
  let : Algebra (MvPolynomial M.indices k) A := M.map.toAlgebra
  let : Algebra.Etale (MvPolynomial M.indices k) A := RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower k (MvPolynomial M.indices k) A :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  have hB : ∀ s ∈ M.boundaryIndices,
      algebraMap (MvPolynomial M.indices k) A (MvPolynomial.X s) ∈ q :=
    M.boundary_coordinates_mem q hw
  have hrel : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k
      (fun s : M.boundaryIndices => M.map (MvPolynomial.X s.val)) J (n + 1) = ⊤ :=
    (M.iterated_logarithmic_coordinates J (n + 1)).symm.trans hbound
  obtain ⟨z, i, hzlog, hzq, hi, hiz⟩ :=
    Relative.LogarithmicTransverseEquation.Construction.exists_etale_relative_logarithmic_transverse_equation M.boundaryIndices q hB J n hJ hrel
  have hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n :=
    (Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal_le_relative k
      (fun s : M.boundaryIndices => M.map (MvPolynomial.X s.val)) J n) hzlog
  obtain ⟨f, d, φ, η, hφ, hφk, hZ, hW, hη⟩ :=
    Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etale_transverse_hypersurface_coordinates_at_point M.boundaryIndices i hi z q hiz
  let E : Derivation k A A := Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) i
  have hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w := by
    rw [M.logarithmic_coordinates]
    intro s
    change Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) i
      (algebraMap (MvPolynomial M.indices k) A (MvPolynomial.X s.val)) ∈ _
    have his : i ≠ s.val := fun h => hi (h ▸ s.property)
    rw [Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X, ite_eq_right his]
    exact Ideal.zero_mem _
  exact ⟨z, E, f, d, φ, η, hz, hzq, hiz, hE, hφ, hφk, hZ, hW, hη⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.LogarithmicHypersurface.Construction
