import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalNormSections

/-! # Norm Frame Basis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! Affine frames with a fixed finite-free rank form a basis as soon
as they cover. The basis and frame on every smaller affine open are
constructed by pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
variable {X Y : Scheme.{u}} {q : X ⟶ Y} [IsFinite q] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y} {d : ℕ}

def LocalNormSections.Construction.NormFrameOpen.restrictAffine (U : LocalNormSections.Construction.NormFrameOpen q L d)
    (V : Y.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U.openSet) : LocalNormSections.Construction.NormFrameOpen q L d := by
  have : IsAffine V.toScheme := hV
  have : IsAffine U.openSet.toScheme := U.affine
  exact ⟨V, hV, (Quotients.FiniteDescent.AffineBasis.Construction.AffineBasisTransfer.restrictLE q V U.openSet hVU U.basis).some,
    (L.frameRestrict hVU U.frame.symm).symm⟩

theorem NormFrameBasis.Construction.normFrameOpens_isBasis
    (hcover : ∀ y : Y, ∃ U : LocalNormSections.Construction.NormFrameOpen q L d, y ∈ U.openSet) :
    Opens.IsBasis (Set.range (fun U : LocalNormSections.Construction.NormFrameOpen q L d => U.openSet)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V y hy
  obtain ⟨U, hyU⟩ := hcover y
  obtain ⟨_, ⟨W : Y.Opens, hW, rfl⟩, hyW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ V ⊓ U.openSet from ⟨hy, hyU⟩) (V ⊓ U.openSet).isOpen
  exact ⟨W, ⟨U.restrictAffine W hW (hWV.trans inf_le_right), rfl⟩,
    hyW, hWV.trans inf_le_left⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
