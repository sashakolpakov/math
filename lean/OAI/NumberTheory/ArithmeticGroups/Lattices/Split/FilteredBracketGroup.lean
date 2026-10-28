import OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredOperatorProjection
import OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingExponentialSubgroup
import OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedSubgroupPreimageImage

/-! # Filtered Bracket Group -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredBracketGroup.Construction

noncomputable section

/-! The bracket automorphisms preserving the weight filtration and
having diagonal blocks in the split exponential subgroup form a closed group. -/

open scoped Classical _root_.Matrix.Norms.Operator

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def splitFilteredBracketUnitGroup {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L)
    (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ) (a : Submodule ℝ (L →L[ℝ] L))
    (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) : Subgroup (L →L[ℝ] L)ˣ :=
  UnipotentBracketGroup.Construction.continuousBracketUnitGroup B ⊓
    (((CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup a hc).comap (FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection b w)).map
      (FilteredOperatorProjection.Construction.weightFilteredOperatorUnits b w).subtype)

theorem splitFilteredBracketUnitGroup_isClosed {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L)
    (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ) (a : Submodule ℝ (L →L[ℝ] L))
    (ha : ∀ X ∈ a, X.toLinearMap.IsSymmetric)
    (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) :
    IsClosed (splitFilteredBracketUnitGroup B b w a hc : Set (L →L[ℝ] L)ˣ) :=
  (UnipotentBracketGroup.Construction.continuousBracketUnitGroup_isClosed B).inter
    (ClosedSubgroupPreimageImage.Construction.closed_subgroup_preimage_image (FilteredOperatorProjection.Construction.weightFilteredOperatorUnits b w)
      (FilteredOperatorProjection.Construction.weightFilteredOperatorUnits_isClosed b w) (FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection b w)
      (FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection_continuous b w) (CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup a hc)
      (CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup_isClosed a ha hc))

theorem mem_splitFilteredBracketUnitGroup_iff {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L)
    (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ) (a : Submodule ℝ (L →L[ℝ] L))
    (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) (g : (L →L[ℝ] L)ˣ) :
    g ∈ splitFilteredBracketUnitGroup B b w a hc ↔
      g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B ∧ ∃ hg : g ∈ FilteredOperatorProjection.Construction.weightFilteredOperatorUnits b w,
        FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection b w ⟨g, hg⟩ ∈ CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup a hc := by
  constructor
  · rintro ⟨hgB, u, hu, rfl⟩
    exact ⟨hgB, u.property, hu⟩
  · rintro ⟨hgB, hgF, hgA⟩
    exact ⟨hgB, ⟨⟨g, hgF⟩, hgA, rfl⟩⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredBracketGroup.Construction
