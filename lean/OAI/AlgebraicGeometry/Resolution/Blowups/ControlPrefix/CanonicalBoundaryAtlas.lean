import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CanonicalLabels
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.Bounds
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Labels
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HistorySurjective

/-! # Canonical Boundary Atlas -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Canonically numbered endpoint boundaries retain their actual normal-crossing atlas and logarithmic bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.canonicalBoundary_atlas
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (hP : P.boundaryCompatible β D) :
    Nonempty (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas g (P.canonicalBoundary D) [Finset.univ]) := by
  obtain ⟨A⟩ := P.endpointBoundary_atlas D hP
  let e := P.endpointLabelsEquiv β
  refine ⟨A.pullbackLabels (fun l => some (e.symm l)) ?_ (P.canonicalBoundary D) (fun _ => rfl)⟩
  intro i j s hi hj
  exact e.symm.injective (Option.some_injective _ (hi.trans hj.symm))

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_canonical_logarithmic_bound
    {b : ℕ} {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (hP : P.boundaryCompatible β D)
    (G : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (hG : G.logarithmicIdeal J b = ⊤) :
    ∃ G' : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas g (P.canonicalBoundary D), G'.logarithmicIdeal K b = ⊤ := by
  obtain ⟨B, hB⟩ := P.exists_endpoint_logarithmic_bound β D hP G hG
  let e := (P.endpointLabelsEquiv β).symm
  refine ⟨B.reindex e.toEmbedding, ?_⟩
  exact (B.logarithmicIdeal_surjective_reindex e.toEmbedding e.surjective K b).trans hB

end

end OAI.AlgebraicGeometry.Resolution.Blowups
