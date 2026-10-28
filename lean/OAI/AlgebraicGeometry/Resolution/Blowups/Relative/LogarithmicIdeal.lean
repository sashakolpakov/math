import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicBoundaryReindex

/-! # Logarithmic Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicIdeal.Construction

noncomputable section

/-! Boundary-tangent differential ideals relative to the fixed coefficient ring. -/

variable (k : Type*) {R ι : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- Derivations over the coefficient ring preserving every boundary equation's ideal. -/
def relativeLogarithmicDerivations (w : ι → R) : Submodule R (Derivation k R R) where
  carrier := {D | ∀ i, D (w i) ∈ Ideal.span {w i}}
  zero_mem' i := by simp
  add_mem' hD hE i := by
    change _ + _ ∈ Ideal.span {w i}
    exact (Ideal.span {w i}).add_mem (hD i) (hE i)
  smul_mem' r D hD i := by
    change r • D (w i) ∈ Ideal.span {w i}
    exact (Ideal.span {w i}).smul_mem r (hD i)

def firstRelativeLogarithmicDifferentialIdeal (w : ι → R) (J : Ideal R) : Ideal R :=
  J ⊔ Ideal.span (Set.range
    (fun t : relativeLogarithmicDerivations k w × J => t.1.val t.2.val))

def iteratedRelativeLogarithmicDifferentialIdeal (w : ι → R) (J : Ideal R) : ℕ → Ideal R
  | 0 => J
  | n + 1 => iteratedRelativeLogarithmicDifferentialIdeal w
      (firstRelativeLogarithmicDifferentialIdeal k w J) n

theorem le_firstRelativeLogarithmicDifferentialIdeal (w : ι → R) (J : Ideal R) :
    J ≤ firstRelativeLogarithmicDifferentialIdeal k w J := le_sup_left

theorem relative_logarithmic_derivation_mem_first (w : ι → R) (J : Ideal R)
    (D : relativeLogarithmicDerivations k w) {p : R} (hp : p ∈ J) :
    D.val p ∈ firstRelativeLogarithmicDifferentialIdeal k w J :=
  Submodule.mem_sup_right (Ideal.subset_span ⟨⟨D, ⟨p, hp⟩⟩, rfl⟩)

theorem firstRelativeLogarithmicDifferentialIdeal_mono (w : ι → R)
    {J L : Ideal R} (h : J ≤ L) :
    firstRelativeLogarithmicDifferentialIdeal k w J ≤
      firstRelativeLogarithmicDifferentialIdeal k w L := by
  apply sup_le
  · exact h.trans (le_firstRelativeLogarithmicDifferentialIdeal k w L)
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨D, p⟩, rfl⟩
    exact relative_logarithmic_derivation_mem_first k w L D (h p.property)

theorem firstRelativeLogarithmicDifferentialIdeal_le_relative (w : ι → R) (J : Ideal R) :
    firstRelativeLogarithmicDifferentialIdeal k w J ≤ DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J := by
  apply sup_le
  · exact DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k J
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨D, p⟩, rfl⟩
    exact DifferentialBlowup.Construction.relative_derivation_mem_first k J D.val p.property

theorem iteratedRelativeLogarithmicDifferentialIdeal_mono (w : ι → R) (n : ℕ)
    {J L : Ideal R} (h : J ≤ L) :
    Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n ≤
      Construction.iteratedRelativeLogarithmicDifferentialIdeal k w L n := by
  induction n generalizing J L with
  | zero => exact h
  | succ n ih => exact ih (firstRelativeLogarithmicDifferentialIdeal_mono k w h)

theorem iteratedRelativeLogarithmicDifferentialIdeal_le_relative (w : ι → R)
    (J : Ideal R) (n : ℕ) :
    Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n ≤
      DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n := by
  induction n generalizing J with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih (firstRelativeLogarithmicDifferentialIdeal k w J)).trans
      (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k n
        (firstRelativeLogarithmicDifferentialIdeal_le_relative k w J))

theorem first_iteratedRelativeLogarithmicDifferentialIdeal (w : ι → R) (J : Ideal R) (n : ℕ) :
    firstRelativeLogarithmicDifferentialIdeal k w
        (Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n) =
      Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J (n + 1) := by
  induction n generalizing J with
  | zero => rfl
  | succ n ih => exact ih (firstRelativeLogarithmicDifferentialIdeal k w J)

/-- With no boundary, the relative logarithmic ideal is exactly the intrinsic
relative differential ideal used for homogenization. -/
theorem firstRelativeLogarithmicDifferentialIdeal_empty [IsEmpty ι] (w : ι → R) (J : Ideal R) :
    firstRelativeLogarithmicDifferentialIdeal k w J = DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J := by
  apply le_antisymm (firstRelativeLogarithmicDifferentialIdeal_le_relative k w J)
  apply sup_le (le_firstRelativeLogarithmicDifferentialIdeal k w J)
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨D, p⟩, rfl⟩
  exact relative_logarithmic_derivation_mem_first k w J ⟨D, fun i => isEmptyElim i⟩ p.property

theorem iteratedRelativeLogarithmicDifferentialIdeal_empty [IsEmpty ι]
    (w : ι → R) (J : Ideal R) (n : ℕ) :
    Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n =
      DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n := by
  induction n generalizing J with
  | zero => rfl
  | succ n ih =>
    simp only [Construction.iteratedRelativeLogarithmicDifferentialIdeal, DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal]
    rw [ih, firstRelativeLogarithmicDifferentialIdeal_empty]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicIdeal.Construction
