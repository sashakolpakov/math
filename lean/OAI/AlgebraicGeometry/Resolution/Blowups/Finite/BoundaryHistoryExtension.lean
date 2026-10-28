import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.OptionalBoundaryLabels

/-! # Boundary History Extension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.BoundaryHistoryExtension.Construction

noncomputable section

/-! Extend the selected history by a cleared unit component and decrease the remaining old-label count. -/

universe u v t

def extendSelectedBoundaryHistory {ι : Type v} {κ : Type t}
    (e : κ ↪ ι) (j : ι) (hj : ∀ s, j ≠ e s) : Option κ ↪ ι where
  toFun a := match a with | none => j | some s => e s
  inj' a b h := by
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some s => exact False.elim (hj s h)
    | some s =>
        cases b with
        | none => exact False.elim (hj s h.symm)
        | some t => exact congrArg some (e.injective h)

theorem excluded_boundary_label_optionMap {ι : Type v} {κ : Type t}
    (e : κ ↪ ι) (j : ι) (hj : ∀ s, j ≠ e s) :
    ∀ s : Option κ, some j ≠ Function.Embedding.optionMap e s := by
  intro s h
  cases s with
  | none => cases h
  | some s => exact hj s (Option.some.inj h)

theorem remaining_boundary_count_option {ι : Type v} {κ : Type t} [Fintype ι] [Fintype κ] :
    Fintype.card (Option ι) - Fintype.card (Option κ) = Fintype.card ι - Fintype.card κ := by
  simp only [Fintype.card_option, Nat.add_sub_add_right]

theorem remaining_boundary_count_extend_lt {ι : Type v} {κ : Type t} [Fintype ι] [Fintype κ]
    (e : κ ↪ ι) (j : ι) (hj : ∀ s, j ≠ e s) :
    Fintype.card ι - Fintype.card (Option κ) < Fintype.card ι - Fintype.card κ := by
  have hcard : Fintype.card κ < Fintype.card ι :=
    Fintype.card_lt_of_injective_of_notMem e e.injective (by
      rintro ⟨s, hs⟩
      exact hj s hs.symm)
  rw [Fintype.card_option]
  omega

theorem relativeLogarithmicDerivations_extend_unit_history
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    {ι : Type v} {κ : Type t} (w : ι → R) (e : κ ↪ ι) (j : ι) (hj : ∀ s, j ≠ e s)
    (hu : IsUnit (w j)) :
    Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun s => w (extendSelectedBoundaryHistory e j hj s)) =
      Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun s => w (e s)) := by
  ext D
  change (∀ s : Option κ, D (w (extendSelectedBoundaryHistory e j hj s)) ∈
      Ideal.span {w (extendSelectedBoundaryHistory e j hj s)}) ↔
    ∀ s : κ, D (w (e s)) ∈ Ideal.span {w (e s)}
  constructor
  · intro h s
    exact h (some s)
  · intro h s
    cases s with
    | none =>
        change D (w j) ∈ Ideal.span {w j}
        rw [Ideal.span_singleton_eq_top.mpr hu]
        exact Submodule.mem_top
    | some s => exact h s

theorem iteratedRelativeLogarithmicDifferentialIdeal_extend_unit_history
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    {ι : Type v} {κ : Type t} (w : ι → R) (e : κ ↪ ι) (j : ι) (hj : ∀ s, j ≠ e s)
    (hu : IsUnit (w j)) (J : Ideal R) (n : ℕ) :
    Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k (fun s => w (extendSelectedBoundaryHistory e j hj s)) J n =
      Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k (fun s => w (e s)) J n :=
  Relative.LogarithmicBoundary.Construction.iteratedRelativeLogarithmicDifferentialIdeal_congr_derivations k _ _
    (relativeLogarithmicDerivations_extend_unit_history w e j hj hu) J n

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.BoundaryHistoryExtension.Construction
