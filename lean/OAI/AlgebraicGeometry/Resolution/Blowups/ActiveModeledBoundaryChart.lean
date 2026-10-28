import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.LogarithmicHypersurface
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.ModelRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.Logarithmic
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PrimeOrderNaturality

/-! # Active Modeled Boundary Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ActiveModeledBoundaryChart.Construction

noncomputable section

/-! Actual pointed opens retaining exactly the active original boundary labels and their logarithmic bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

structure ActiveModeledBoundaryOpenChart (k : Type u) [CommRing k]
    (R : CommRingCat.{u}) [Algebra k R] {ι : Type v} (w : ι → R)
    (J : Ideal R) (m : ℕ) (p : PrimeSpectrum R) where
  denominator : R
  denominator_not_mem : denominator ∉ p.asIdeal
  active : Finset ι
  active_iff : ∀ j, j ∈ active ↔ w j ∈ p.asIdeal
  point : PrimeSpectrum (Localization.Away denominator)
  point_over : PrimeSpectrum.comap (algebraMap R (Localization.Away denominator)) point = p
  inactive_units : ∀ j, j ∉ active → IsUnit (algebraMap R (Localization.Away denominator) (w j))
  model : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k (Localization.Away denominator) active
    (fun j => algebraMap R (Localization.Away denominator) (w j.val))
  logarithmicBound : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k
    (fun j : active => algebraMap R (Localization.Away denominator) (w j.val))
    (J.map (algebraMap R (Localization.Away denominator))) m = ⊤

/-- Isolating the active original labels uses an actual localization,
preserves the original prime, and carries both the boundary model and
the stronger relative logarithmic order bound to that open. -/
theorem exists_active_modeled_boundary_open_chart {k : Type u} [CommRing k]
    (R : CommRingCat.{u}) [Algebra k R] {ι : Type v} [Fintype ι]
    (w : ι → R) (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (J : Ideal R) (m : ℕ)
    (p : PrimeSpectrum R)
    (hbound : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J m = ⊤) :
    Nonempty (ActiveModeledBoundaryOpenChart k R w J m p) := by
  classical
  have hs : Function.Surjective (fun j : (Finset.univ : Finset ι) => j.val) :=
    fun j => ⟨⟨j, Finset.mem_univ j⟩, rfl⟩
  have hfull : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k
      (fun j : (Finset.univ : Finset ι) => w j.val) J m = ⊤ :=
    (Relative.LogarithmicBoundary.Construction.iteratedRelativeLogarithmicDifferentialIdeal_surjective_reindex k w _ hs J m).trans hbound
  obtain ⟨B, t, _, ht, hactive, hunit, hlog⟩ := Relative.Logarithmic.Construction.exists_relative_active_boundary_neighborhood
    k w Finset.univ J p.asIdeal m hfull
  obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime t p ht
  let f : R →ₐ[k] Localization.Away t := IsScalarTower.toAlgHom k R (Localization.Away t)
  have hf : f.toRingHom.Etale := RingHom.etale_algebraMap.mpr inferInstance
  let e : B ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  exact ⟨{ denominator := t
           denominator_not_mem := ht
           active := B
           active_iff := fun j => hactive j (Finset.mem_univ j)
           point := Q
           point_over := hQ
           inactive_units := fun j hj => hunit j (Finset.mem_univ j) hj
           model := (M.reindex e).baseChange f hf
           logarithmicBound := hlog }⟩

variable {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
  {ι : Type v} {w : ι → R} {J : Ideal R} {m : ℕ} {p : PrimeSpectrum R}

theorem ActiveModeledBoundaryOpenChart.active_equations_mem
    (C : ActiveModeledBoundaryOpenChart k R w J m p) (j : C.active) :
    algebraMap R (Localization.Away C.denominator) (w j.val) ∈ C.point.asIdeal := by
  have hq : C.point.asIdeal.comap (algebraMap R (Localization.Away C.denominator)) = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal C.point_over
  change w j.val ∈ C.point.asIdeal.comap (algebraMap R (Localization.Away C.denominator))
  rw [hq]
  exact (C.active_iff j.val).mp j.property

/-- The chosen open has exactly the original ideal order at the lifted
prime; passing to the active boundary chart does not lose the order condition. -/
theorem ActiveModeledBoundaryOpenChart.local_order
    (C : ActiveModeledBoundaryOpenChart k R w J m p)
    (hJ : J.map (algebraMap R (Localization.AtPrime p.asIdeal)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ m) :
    (J.map (algebraMap R (Localization.Away C.denominator))).map
        (algebraMap (Localization.Away C.denominator) (Localization.AtPrime C.point.asIdeal)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime C.point.asIdeal) ^ m := by
  have hf : (algebraMap R (Localization.Away C.denominator)).Etale :=
    RingHom.etale_algebraMap.mpr inferInstance
  have hq : C.point.asIdeal.comap (algebraMap R (Localization.Away C.denominator)) = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal C.point_over
  exact (Blowups.Etale.PrimeOrderNaturality.Construction.etale_map_prime_order_iff _ hf J p.asIdeal C.point.asIdeal hq.symm m).mpr hJ

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ActiveModeledBoundaryChart.Construction
