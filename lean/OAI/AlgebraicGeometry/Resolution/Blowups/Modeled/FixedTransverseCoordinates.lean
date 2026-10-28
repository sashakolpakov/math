import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.LogarithmicHypersurface

/-! # Fixed Transverse Coordinates -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.FixedTransverseCoordinates.Construction

noncomputable section

/-! Retain a specified transverse equation while adapting the complete active boundary. -/

universe u v

variable {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R]
  {w : ι → R}

/-- A supplied boundary-tangent derivative detects coordinates retaining
the specified normal equation itself, at any prime where it is transverse. -/
theorem exists_modeled_fixed_transverse_coordinates (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (q : Ideal R) [q.IsPrime] (hw : ∀ j, w j ∈ q)
    (E : Derivation k R R) (hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w)
    (z : R) (hEz : E z ∉ q) :
    ∃ (D : Derivation k R R) (f : DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (d : ℕ)
      (φ : MvPolynomial (Fin d ⊕ Option M.boundaryIndices) k →+* Localization.Away f)
      (η : Localization.Away f →+* q.ResidueField),
      φ.Etale ∧ (∀ c : k, φ (MvPolynomial.C c) = algebraMap k (Localization.Away f) c) ∧
      φ (MvPolynomial.X (Sum.inr none)) = algebraMap R (Localization.Away f) z ∧
      (∀ s : M.boundaryIndices, φ (MvPolynomial.X (Sum.inr (some s))) =
        algebraMap R (Localization.Away f) (M.map (MvPolynomial.X s.val))) ∧
      ∀ r : R, η (algebraMap R (Localization.Away f) r) = algebraMap R q.ResidueField r := by
  let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
  let : Algebra.Etale (MvPolynomial M.indices k) R := RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower k (MvPolynomial M.indices k) R :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  have hB : ∀ s ∈ M.boundaryIndices,
      algebraMap (MvPolynomial M.indices k) R (MvPolynomial.X s) ∈ q :=
    M.boundary_coordinates_mem q hw
  have hEco : ∀ s ∈ M.boundaryIndices,
      E (algebraMap (MvPolynomial M.indices k) R (MvPolynomial.X s)) ∈
        Ideal.span {algebraMap (MvPolynomial M.indices k) R (MvPolynomial.X s)} := by
    rw [M.logarithmic_coordinates] at hE
    intro s hs
    exact hE ⟨s, hs⟩
  obtain ⟨i, hi, hiz⟩ := Relative.LogarithmicTransverseEquation.Construction.relative_logarithmic_derivative_detects_transverse_direction
    M.boundaryIndices q hB E hEco z hEz
  obtain ⟨f, d, φ, η, hφ, hg, hZ, hW, hη⟩ :=
    Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etale_transverse_hypersurface_coordinates_at_point M.boundaryIndices i hi z q hiz
  exact ⟨Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) i, f, d, φ, η, hφ, hg, hZ, hW, hη⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.FixedTransverseCoordinates.Construction
