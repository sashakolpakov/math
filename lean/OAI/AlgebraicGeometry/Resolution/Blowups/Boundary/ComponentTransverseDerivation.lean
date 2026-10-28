import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.ModelRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.LogarithmicCoordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ModuleDerivations

/-! # Component Transverse Derivation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A boundary component has a transverse derivation tangent to every other retained component. -/

universe u v t

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.exists_component_transverse_derivation
    {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    {ι : Type v} {κ : Type t} {w : ι → R} (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (j : ι) (e : κ ↪ ι) (hne : ∀ l, j ≠ e l)
    (p : PrimeSpectrum R) (hw : w j ∈ p.asIdeal) :
    ∃ D : Derivation k R R,
      D ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun l => w (e l)) ∧ D (w j) ∉ p.asIdeal := by
  cases hcoord : M.coordinate j with
  | none =>
      have hu : IsUnit (w j) := by
        rw [M.equation j, hcoord, mul_one]
        exact M.multiplierUnit j
      exact False.elim (p.asIdeal.notMem_of_isUnit hu hw)
  | some s =>
      let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
      let : IsScalarTower k (MvPolynomial M.indices k) R :=
        IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
      let : Algebra.Etale (MvPolynomial M.indices k) R := RingHom.etale_algebraMap.mp M.etale
      let z := M.map (MvPolynomial.X s)
      let D : Derivation k R R := Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) s
      have heq : w j = M.multiplier j * z := by simpa only [hcoord] using M.equation j
      have hz : z ∈ p.asIdeal := by
        apply (p.asIdeal.unit_mul_mem_iff_mem (M.multiplierUnit j)).mp
        rwa [← heq]
      have hD : D ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun l => w (e l)) := by
        rw [(M.reindex e).logarithmic_coordinateEquation]
        intro l
        cases hl : M.coordinate (e l) with
        | none =>
            change D ((M.reindex e).coordinateEquation l) ∈ _
            simp only [Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateEquation, Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel.reindex, hl]
            rw [Derivation.map_one_eq_zero]
            exact Ideal.zero_mem _
        | some t =>
            have hst : s ≠ t := by
              intro h
              apply hne l
              exact M.distinct j (e l) s hcoord (hl.trans (congrArg some h.symm))
            simp only [Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateEquation, Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel.reindex, hl]
            change Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) s
              (algebraMap (MvPolynomial M.indices k) R (MvPolynomial.X t)) ∈ _
            rw [Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X, ite_eq_right hst]
            exact Ideal.zero_mem _
      have hDz : D z = 1 := by
        change Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) s
          (algebraMap (MvPolynomial M.indices k) R (MvPolynomial.X s)) = 1
        rw [Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X, ite_eq_left rfl]
      refine ⟨D, hD, ?_⟩
      intro h
      rw [heq, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hDz, mul_one] at h
      have hp : z * D (M.multiplier j) ∈ p.asIdeal := p.asIdeal.mul_mem_right _ hz
      have hu : M.multiplier j ∈ p.asIdeal := (p.asIdeal.add_mem_iff_left hp).mp h
      exact p.asIdeal.notMem_of_isUnit (M.multiplierUnit j) hu

end

end OAI.AlgebraicGeometry.Resolution.Blowups
