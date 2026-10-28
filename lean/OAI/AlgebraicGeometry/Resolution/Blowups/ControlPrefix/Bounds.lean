import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.Boundary
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.LogarithmicBlowupBound
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Dimension

/-! # Bounds -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Dimension and full logarithmic order bounds persist along actual permissible prefixes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.endpoint_dimension_le
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    (d : ℕ) (hd : topologicalKrullDim X ≤ d) : topologicalKrullDim Y ≤ d := by
  revert hd
  revert ‹Smooth f›
  induction P with
  | stop => intro _ hd; exact hd
  | @blowup X hX hN f J I hI hb hp hs hbl Y g K tail ih =>
      intro hf hd
      let : Smooth f := hf
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
      exact ih (GlobalBlowup.Dimension.Construction.globalBlowup_dimension_le f I hI d hd)

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_endpoint_logarithmic_bound
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
      (β : Type) [Fintype β] (D : β → X.IdealSheafData), P.boundaryCompatible β D →
      ∀ G : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D, G.logarithmicIdeal J b = ⊤ →
      ∃ G' : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas g (P.endpointBoundary D), G'.logarithmicIdeal K b = ⊤ := by
  induction P with
  | stop =>
      intro _ _ _ β _ D _ G hG
      exact ⟨G, hG⟩
  | @blowup X hX hN f J I hI hb hp hs hbl Y g K tail ih =>
      intro _ _ hcompact β _ D hD G hG
      let : CompactSpace X := hcompact
      let : CompactSpace (GlobalBlowup.Data.Construction.globalBlowup I hI) := QuasiCompact.compactSpace_of_compactSpace (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
      obtain ⟨A⟩ := hD.1
      obtain ⟨G₁⟩ := (A.blowupBoundary hI).exists_modelAtlas
      have hG₁ := Global.LogarithmicBlowupBound.Construction.globalBlowup_preserves_logarithmic_order_bound I J hI D A G G₁ b hp hG
      exact ih (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) hD.2 G₁ hG₁

end

end OAI.AlgebraicGeometry.Resolution.Blowups
