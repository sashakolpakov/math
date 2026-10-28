import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing

/-! # Section Overlap -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionOverlap.Construction.SectionOverlapGluing

noncomputable section

/-! Gluing module sections using named overlap opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing

universe u v

theorem glue {X : Scheme.{u}} (M : X.Modules) {ι : Type v}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (W : ι → ι → X.Opens) (hWL : ∀ i j, W i j ≤ U i) (hWR : ∀ i j, W i j ≤ U j)
    (hW : ∀ i j, W i j = U i ⊓ U j) (s : ∀ i, Γ(M, U i))
    (hs : ∀ i j,
      M.presheaf.map (homOfLE (hWL i j)).op (s i) =
        M.presheaf.map (homOfLE (hWR i j)).op (s j)) :
    ∃! t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M, ∀ i, t.app (U i) (1 : Γ(X, U i)) = s i := by
  apply AbelianModuli.HilbertConstruction.Section.Gluing.moduleSection_glue M U hU s
  intro i j
  have h := congrArg (M.presheaf.map (homOfLE (hW i j).ge).op) (hs i j)
  rw [← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply] at h
  have hl : (homOfLE (hWL i j)).op ≫ (homOfLE (hW i j).ge).op =
      (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op := Subsingleton.elim _ _
  have hr : (homOfLE (hWR i j)).op ≫ (homOfLE (hW i j).ge).op =
      (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op := Subsingleton.elim _ _
  rw [hl, hr] at h
  exact h

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionOverlap.Construction.SectionOverlapGluing
