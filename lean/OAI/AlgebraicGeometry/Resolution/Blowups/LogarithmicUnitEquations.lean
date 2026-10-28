import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicBoundary

/-! # Logarithmic Unit Equations -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicUnitEquations.Construction

noncomputable section

/-! Logarithmic tangency depends on the boundary ideals, not their invertible equation factors. -/

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- Multiplying an equation by a unit does not change its logarithmic
tangency condition for any derivation over the original ground ring. -/
theorem derivation_unit_equation_mem_iff (D : Derivation k R R) (z u : R) (hu : IsUnit u) :
    D (u * z) ∈ Ideal.span {u * z} ↔ D z ∈ Ideal.span {z} := by
  rw [Ideal.span_singleton_mul_left_unit hu]
  have hterm : z * D u ∈ Ideal.span {z} :=
    Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self z)
  have he : D (u * z) = u * D z + z * D u := by
    rw [Derivation.leibniz]
    rfl
  rw [he]
  constructor
  · intro h
    apply (Ideal.unit_mul_mem_iff_mem _ hu).mp
    have hs := (Ideal.span {z}).sub_mem h hterm
    simpa only [add_sub_cancel_right] using hs
  · intro h
    exact (Ideal.span {z}).add_mem ((Ideal.span {z}).mul_mem_left u h) hterm

theorem relativeLogarithmicDerivations_mul_units (k : Type*) [CommRing k]
    {R ι : Type*} [CommRing R] [Algebra k R]
    (w u : ι → R) (hu : ∀ j, IsUnit (u j)) :
    Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun j => u j * w j) = Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w := by
  ext D
  change (∀ j, D (u j * w j) ∈ Ideal.span {u j * w j}) ↔
    ∀ j, D (w j) ∈ Ideal.span {w j}
  constructor
  · intro h j
    exact (derivation_unit_equation_mem_iff D (w j) (u j) (hu j)).mp (h j)
  · intro h j
    exact (derivation_unit_equation_mem_iff D (w j) (u j) (hu j)).mpr (h j)

theorem iteratedRelativeLogarithmicDifferentialIdeal_mul_units (k : Type*) [CommRing k]
    {R ι : Type*} [CommRing R] [Algebra k R]
    (w u : ι → R) (hu : ∀ j, IsUnit (u j)) (J : Ideal R) (n : ℕ) :
    Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k (fun j => u j * w j) J n =
      Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n :=
  Relative.LogarithmicBoundary.Construction.iteratedRelativeLogarithmicDifferentialIdeal_congr_derivations k _ _
    (relativeLogarithmicDerivations_mul_units k w u hu) J n

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicUnitEquations.Construction
