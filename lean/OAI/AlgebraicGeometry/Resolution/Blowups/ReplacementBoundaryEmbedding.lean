import OAI.AlgebraicGeometry.Resolution.Blowups.ReplacedCenterCoordinateIndices

/-! # Replacement Boundary Embedding -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ReplacementBoundaryEmbedding.Construction

noncomputable section

/-! Retained boundary coordinates keep their exact center membership after a transverse replacement. -/

universe u

def replacementBoundaryEmbedding {σ : Type u} (B : Finset σ) (i : σ) (hi : i ∉ B) :
    B ↪ Option {j : σ // i ≠ j} where
  toFun s := some ⟨s.val, fun h => hi (h.symm ▸ s.property)⟩
  inj' _a _b h := Subtype.ext (congrArg (fun s : {j : σ // i ≠ j} => s.val) (Option.some.inj h))

theorem replacementBoundaryEmbedding_ne_none {σ : Type u}
    (B : Finset σ) (i : σ) (hi : i ∉ B) (s : B) :
    replacementBoundaryEmbedding B i hi s ≠ none := by
  intro h
  cases h

theorem replacement_boundary_center_iff {σ : Type u} [Fintype σ] [DecidableEq σ]
    (C B : Finset σ) (i : C) (hi : i.val ∉ B) (b : Option B) :
    (∃ s ∈ Finset.univ.image (ReplacedCenterCoordinateIndices.Construction.centerReplacementCoordinateEmbedding C i),
      b.map (replacementBoundaryEmbedding B i.val hi) = some s) ↔
      ∃ s ∈ C, b.map Subtype.val = some s := by
  cases b with
  | none => simp
  | some b =>
      simp only [Option.map_some, Option.some.injEq]
      have hm := ReplacedCenterCoordinateIndices.Construction.centerReplacementCoordinateEmbedding_mem_iff C i
        ⟨b.val, fun h => hi (h.symm ▸ b.property)⟩
      constructor
      · rintro ⟨s, hs, he⟩
        have hb : replacementBoundaryEmbedding B i.val hi b ∈
            Finset.univ.image (ReplacedCenterCoordinateIndices.Construction.centerReplacementCoordinateEmbedding C i) := he.symm ▸ hs
        exact ⟨b.val, hm.mp hb, rfl⟩
      · rintro ⟨s, hs, he⟩
        exact ⟨replacementBoundaryEmbedding B i.val hi b, hm.mpr (he.symm ▸ hs), rfl⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ReplacementBoundaryEmbedding.Construction
