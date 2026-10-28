import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ClosedComplement

/-! # Complement Induction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ComplementInduction.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual complement of a nonempty chart has strictly smaller closed image -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {U Z X : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
    (u : U ⟶ Z) [IsOpenImmersion u]

def openComplementImageClosed : Closeds X :=
  ⟨Set.range (Open.ClosedComplement.BundleCycles.openComplementInclusion u ≫ i),
    (Open.ClosedComplement.BundleCycles.openComplementInclusion u ≫ i).isClosedEmbedding.isClosed_range⟩

theorem openComplementImageClosed_lt (S : Closeds X) (hi : Set.range i = (S : Set X))
    (z : Z) (hz : z ∈ Set.range u) : openComplementImageClosed i u < S := by
  apply lt_of_le_of_ne
  · intro x hx
    obtain ⟨w, rfl⟩ := hx
    change i (Open.ClosedComplement.BundleCycles.openComplementInclusion u w) ∈ (S : Set X)
    rw [← hi]
    exact ⟨Open.ClosedComplement.BundleCycles.openComplementInclusion u w, rfl⟩
  · intro he
    have hm : i z ∈ openComplementImageClosed i u := by
      rw [he]
      change i z ∈ (S : Set X)
      rw [← hi]
      exact ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hm
    have hw' : Open.ClosedComplement.BundleCycles.openComplementInclusion u w = z := i.isClosedEmbedding.injective hw
    have hk : Open.ClosedComplement.BundleCycles.openComplementInclusion u w ∉ Set.range u := by
      rw [← Set.mem_compl_iff, ← Open.ClosedComplement.BundleCycles.openComplementInclusion_range u]
      exact ⟨w, rfl⟩
    exact hk (hw'.symm ▸ hz)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ComplementInduction.BundleCycles
