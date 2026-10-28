import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.LogarithmicHistory
import OAI.AlgebraicGeometry.Resolution.Blowups.WholePrefixAuxiliaryTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ClearedHistoryNeighborhood

/-! # Auxiliary History Open -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The complement of a transformed old boundary component carries the enlarged fixed-length logarithmic history. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.transformedBoundaryComplement
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {K : X.IdealSheafData} {L : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f K Y g L)
    {β : Type} (D : β → X.IdealSheafData) (j : β) : Y.Opens :=
  (P.transformIdeal (D j) 1).support.compl

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.auxiliary_clearance
    {m : ℕ} (hm : 0 < m) {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {K : X.IdealSheafData} {L : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix m X f K Y g L)
    (J H : X.IdealSheafData) (hK : K = GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H m) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g L (m - 1) = ⊤ →
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g (P.transformIdeal J m) (m - 1) ⊔ P.transformIdeal H 1 = ⊤ := by
  let : Smooth g := P.endpoint_smooth
  intro ht
  obtain ⟨J', H', R, S, hR, hS, hclear⟩ := P.exists_auxiliary_clearance_prefix hm J H hK ht
  rw [hR.transformIdeal, hS.transformIdeal]
  exact hclear

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_fixed_length_extended_history_on_complement
    {m : ℕ} {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β γ : Type} [Fintype β] [Fintype γ]
    (D : β → X.IdealSheafData) (B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D)
    (e : γ ↪ β) (j : β) (hj : ∀ s, j ≠ e s) (J : X.IdealSheafData)
    (hbound : (B.reindex e).logarithmicIdeal J m = ⊤)
    {L : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix m X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) m) Y g L)
    (hP : P.boundaryCompatible β D) (N : ℕ) (hN : P.stepCount = N) :
    ∃ C : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas ((P.transformedBoundaryComplement D j).ι ≫ g)
        (fun l => (P.boundaryAtLength D N hN l).comap (P.transformedBoundaryComplement D j).ι),
      (C.reindex (FixedLengthBoundaryHistory.Construction.iteratedExtendedBoundaryHistory N e j hj)).logarithmicIdeal
        ((P.transformIdeal J m).comap (P.transformedBoundaryComplement D j).ι) m = ⊤ := by
  obtain ⟨E, hE⟩ := P.exists_fixed_length_logarithmic_history D hP B e J le_sup_left hbound N hN
  let : IsLocallyNoetherian Y := E.locallyNoetherian
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace P.toBase
  let : IsNoetherian Y := ⟨⟩
  let U := P.transformedBoundaryComplement D j
  let : NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  obtain ⟨A⟩ := P.boundaryAtLength_atlas D hP N hN
  obtain ⟨C⟩ := (A.comapOpen g (P.transformedBoundaryComplement D j).ι).exists_modelAtlas
  have hu : (P.boundaryAtLength D N hN (ControlPrefix.IdealTransforms.Construction.iteratedInitialBoundaryEmbedding N β j)).comap
      (P.transformedBoundaryComplement D j).ι = ⊤ := by
    rw [P.boundaryAtLength_initialLabel D j N hN]
    exact Global.ResidualNeighborhood.Construction.idealSheaf_comap_supportComplement_eq_top _
  refine ⟨C, ?_⟩
  exact E.logarithmic_bound_extend_history_on_open (FixedLengthBoundaryHistory.Construction.iteratedBoundaryEmbedding N e)
    (ControlPrefix.IdealTransforms.Construction.iteratedInitialBoundaryEmbedding N β j) (FixedLengthBoundaryHistory.Construction.iteratedBoundaryEmbedding_excludes_initial N e j hj)
    (P.transformIdeal J m) m hE (P.transformedBoundaryComplement D j) hu C

end

end OAI.AlgebraicGeometry.Resolution.Blowups
