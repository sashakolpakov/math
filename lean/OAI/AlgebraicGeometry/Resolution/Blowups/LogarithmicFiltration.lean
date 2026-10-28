import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicBoundary

/-! # Logarithmic Filtration -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicFiltration.Construction

noncomputable section

section

/-! Logarithmic differential ideals depend only on the labelled principal ideals. -/

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem derivation_preserves_principal_ideal_iff (D : Derivation k R R) (z : R) :
    (∀ x ∈ Ideal.span {z}, D x ∈ Ideal.span {z}) ↔ D z ∈ Ideal.span {z} := by
  constructor
  · intro h
    exact h z (Ideal.mem_span_singleton_self z)
  · intro h x hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [D.leibniz]
    exact (Ideal.span {z}).add_mem
      ((Ideal.span {z}).mul_mem_right _ (Ideal.mem_span_singleton_self z))
      ((Ideal.span {z}).mul_mem_left _ h)

theorem relativeLogarithmicDerivations_eq_of_principal_ideals
    {ι : Type*} (w v : ι → R) (he : ∀ j, Ideal.span {w j} = Ideal.span {v j}) :
    Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w = Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k v := by
  ext D
  change (∀ j, D (w j) ∈ Ideal.span {w j}) ↔ ∀ j, D (v j) ∈ Ideal.span {v j}
  constructor
  · intro h j
    apply (derivation_preserves_principal_ideal_iff D (v j)).mp
    rw [← he j]
    exact (derivation_preserves_principal_ideal_iff D (w j)).mpr (h j)
  · intro h j
    apply (derivation_preserves_principal_ideal_iff D (w j)).mp
    rw [he j]
    exact (derivation_preserves_principal_ideal_iff D (v j)).mpr (h j)

theorem iteratedRelativeLogarithmicDifferentialIdeal_eq_of_principal_ideals
    {ι : Type*} (w v : ι → R) (he : ∀ j, Ideal.span {w j} = Ideal.span {v j})
    (J : Ideal R) (n : ℕ) :
    Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n =
      Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k v J n :=
  Relative.LogarithmicBoundary.Construction.iteratedRelativeLogarithmicDifferentialIdeal_congr_derivations k w v
    (relativeLogarithmicDerivations_eq_of_principal_ideals w v he) J n

end

/-! Increasing logarithmic filtrations preserve every selected boundary component ideal. -/

variable (k : Type*) {R ι : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem iteratedRelativeLogarithmicDifferentialIdeal_monotone_order
    (w : ι → R) (J : Ideal R) {n m : ℕ} (hnm : n ≤ m) :
    Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n ≤
      Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J m := by
  apply monotone_nat_of_le_succ _ hnm
  intro r
  rw [← Relative.LogarithmicIdeal.Construction.first_iteratedRelativeLogarithmicDifferentialIdeal]
  exact Relative.LogarithmicIdeal.Construction.le_firstRelativeLogarithmicDifferentialIdeal k w _

theorem firstRelativeLogarithmicDifferentialIdeal_component (w : ι → R) (j : ι) :
    Relative.LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w (Ideal.span {w j}) = Ideal.span {w j} := by
  apply le_antisymm _ (Relative.LogarithmicIdeal.Construction.le_firstRelativeLogarithmicDifferentialIdeal k w _)
  apply sup_le le_rfl
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨D, x⟩, rfl⟩
  exact (derivation_preserves_principal_ideal_iff D.val (w j)).mpr (D.property j) x.val x.property

theorem iteratedRelativeLogarithmicDifferentialIdeal_component (w : ι → R) (j : ι) (n : ℕ) :
    Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w (Ideal.span {w j}) n = Ideal.span {w j} := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w
        (Relative.LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w (Ideal.span {w j})) n = _
      rw [firstRelativeLogarithmicDifferentialIdeal_component, ih]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicFiltration.Construction
