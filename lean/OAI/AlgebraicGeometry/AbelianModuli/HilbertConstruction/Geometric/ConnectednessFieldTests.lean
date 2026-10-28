import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.PropertyComparison
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Connectedness Field Tests -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.ConnectednessFieldTests

noncomputable section

/-! A field-valued criterion for geometric connectedness of a family determines the same criterion after arbitrary base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem geometricallyConnected_iterated_pullback_iff {X S T V : Scheme.{u}}
    (p : X ⟶ S) (c : T ⟶ S) (b : V ⟶ T) :
    GeometricallyConnected (pullback.snd (pullback.snd p c) b) ↔
      GeometricallyConnected (pullback.snd p (b ≫ c)) :=
  Cartesian.PropertyComparison.property_cartesian_iff_pullback (@GeometricallyConnected : MorphismProperty Scheme.{u})
    (pullback.fst (pullback.snd p c) b ≫ pullback.fst p c)
    (pullback.snd (pullback.snd p c) b) p (b ≫ c)
    ((IsPullback.of_hasPullback (pullback.snd p c) b).paste_horiz (IsPullback.of_hasPullback p c))

theorem geometricallyConnected_open_field_tests {X S : Scheme.{u}} (p : X ⟶ S) (U : S.Opens)
    (hU : ∀ (K : Type u) [Field K] (c : Spec (.of K) ⟶ S),
      GeometricallyConnected (pullback.snd p c) ↔ Set.range c ⊆ (U : Set S))
    {T : Scheme.{u}} (c : T ⟶ S) :
    GeometricallyConnected (pullback.snd p c) ↔ Set.range c ⊆ (U : Set S) := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  have ht (t : T) : GeometricallyConnected ((pullback.snd p c).fiberToSpecResidueField t) ↔
      c t ∈ U := by
    refine (geometricallyConnected_iterated_pullback_iff p c (T.fromSpecResidueField t)).trans
      ((hU (T.residueField t) (T.fromSpecResidueField t ≫ c)).trans ?_)
    constructor
    · intro h
      let k : Spec (T.residueField t) := (⊥ : PrimeSpectrum (T.residueField t))
      have hk := h ⟨k, rfl⟩
      change c (T.fromSpecResidueField t k) ∈ U at hk
      exact (T.fromSpecResidueField_apply t k) ▸ hk
    · intro h
      rintro s ⟨k, rfl⟩
      change c (T.fromSpecResidueField t k) ∈ U
      rw [T.fromSpecResidueField_apply]
      exact h
  simp_rw [ht]
  exact ⟨fun h _ ⟨t, ht⟩ => ht ▸ h t, fun h t => h ⟨t, rfl⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.ConnectednessFieldTests
