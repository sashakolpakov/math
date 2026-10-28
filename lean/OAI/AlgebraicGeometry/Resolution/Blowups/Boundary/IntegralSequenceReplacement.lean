import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.BoundaryCenterFactorSequence
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.CenterSequenceReplacement

/-! # Integral Sequence Replacement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Compact smooth-center sequences admit integral-center replacements retaining every canonical boundary label. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem Boundary.IntegralSequenceReplacement.Construction.exists_boundary_integral_sequence_of_smooth_center_continuation
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    (I : X.IdealSheafData) (hI : I ≠ ⊥) [Smooth (I.subschemeι ≫ f)]
    [NoetherianSpace I.subscheme] (b : ℕ) (hb : 0 < b) (hp : J ≤ I ^ b)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (R : Global.MonomialSequence.Construction.SmoothFixedControlSequence b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b)) (hR : R.integralCenters)
    (hRB : R.boundaryCompatible (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)) :
    ∃ S : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J, S.integralCenters ∧ S.boundaryCompatible β D := by
  let : Fintype (irreducibleComponents I.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype I
  let e := (Fintype.equivFin (irreducibleComponents I.subscheme)).symm
  let K (i : Fin (Fintype.card (irreducibleComponents I.subscheme))) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I (e i)
  have hprod : I = ∏ i, K i := by
    change I = ∏ i, Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I (e i)
    rw [e.prod_comp, Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_prod]
  exact Finite.BoundaryCenterFactorSequence.Construction.exists_boundary_integral_sequence_of_finite_center_factorization _ X f J hJ b hb I hI K
    (fun i => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_ne_bot f I hI (e i))
    (fun i => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_integral f I (e i))
    (fun i => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_smooth f I (e i))
    (fun i j hij => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_sup f I (e i) (e j) (fun h => hij (e.injective h)))
    hprod inferInstance hp β D A R hR hRB

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.exists_boundary_integral_replacement
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J) [IsIntegral X] [IsLocallyNoetherian X]
    [CompactSpace X] [Smooth f] (hJ : J ≠ ⊥) :
    ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData), T.boundaryCompatible β D →
      ∃ S : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J, S.integralCenters ∧ S.boundaryCompatible β D := by
  revert hJ
  revert ‹Smooth f› ‹CompactSpace X› ‹IsLocallyNoetherian X› ‹IsIntegral X›
  induction T with
  | @terminal Y g hs J ht =>
      intro _ _ _ _ _ β _ D hB
      refine ⟨.terminal ht, ?_, hB⟩
      change True
      trivial
  | @blowup Y hY hN g J I hI hb hp hs hbl tail ih =>
      intro _ _ hcompact hg hJ β _ D hB
      let : CompactSpace Y := hcompact
      let : Smooth g := hg
      let : Smooth (I.subschemeι ≫ g) := hs
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ g) := hbl
      let : CompactSpace (GlobalBlowup.Data.Construction.globalBlowup I hI) := QuasiCompact.compactSpace_of_compactSpace (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
      let : IsNoetherian Y := ⟨⟩
      let : NoetherianSpace I.subscheme := I.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
      obtain ⟨A⟩ := hB.1
      obtain ⟨R, hR, hRB⟩ := ih (GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot I J hI b hJ)
        (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) hB.2
      exact Boundary.IntegralSequenceReplacement.Construction.exists_boundary_integral_sequence_of_smooth_center_continuation g J hJ I hI b hb hp D A R hR hRB

end

end OAI.AlgebraicGeometry.Resolution.Blowups
