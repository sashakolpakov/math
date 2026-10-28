import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.ModelRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.LogarithmicCoordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicPower

/-! # Old Boundary Auxiliary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! An omitted old boundary component supplies the logarithmic bound for its clearance ideal. -/

universe u v t

theorem Modeled.OldBoundaryAuxiliary.Construction.iteratedRelativeLogarithmicDifferentialIdeal_top
    (k : Type*) {R ι : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (w : ι → R) (n : ℕ) :
    Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w (⊤ : Ideal R) n = ⊤ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal,
        Relative.LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal, top_sup_eq] using ih

/-- If the auxiliary ideal contains a power of one omitted boundary
equation, its logarithmic bound relative to all retained labels is automatic.
Original unit factors and unit labels are allowed throughout. -/
theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.old_boundary_auxiliary_logarithmic_bound
    {k R : Type u} [Field k] [CharZero k] [CommRing R] [Algebra k R]
    {ι : Type v} {κ : Type t} {w : ι → R} (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (j : ι) (e : κ ↪ ι) (hne : ∀ l, j ≠ e l)
    (J L : Ideal R) (hw : w j ∈ L) (m : ℕ) :
    Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k (fun l => w (e l))
      (Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J L m) m = ⊤ := by
  cases hcoord : M.coordinate j with
  | none =>
      have hu : IsUnit (w j) := by
        rw [M.equation j, hcoord, mul_one]
        exact M.multiplierUnit j
      have hL : L = ⊤ := Ideal.eq_top_of_isUnit_mem _ hw hu
      have haux : Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J L m = ⊤ := by
        rw [Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal, hL, Ideal.top_pow, sup_top_eq]
      rw [haux]
      exact Modeled.OldBoundaryAuxiliary.Construction.iteratedRelativeLogarithmicDifferentialIdeal_top k _ m
  | some s =>
      let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
      let : IsScalarTower k (MvPolynomial M.indices k) R :=
        IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
      let : Algebra.Etale (MvPolynomial M.indices k) R := RingHom.etale_algebraMap.mp M.etale
      let : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
      let z := M.map (MvPolynomial.X s)
      let D : Derivation k R R := Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) s
      have hz : z ∈ L := by
        apply (L.unit_mul_mem_iff_mem (M.multiplierUnit j)).mp
        simpa only [M.equation j, hcoord] using hw
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
      exact Relative.LogarithmicPower.Construction.relative_logarithmic_bound_of_coordinate_power k _ ⟨D, hD⟩ z hDz _ m
        (Submodule.mem_sup_right (Ideal.pow_mem_pow hz m))

end

end OAI.AlgebraicGeometry.Resolution.Blowups
