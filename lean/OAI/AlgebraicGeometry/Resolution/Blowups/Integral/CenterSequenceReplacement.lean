import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.CenterFactorSequence
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterComponents

/-! # Center Sequence Replacement -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Resolution.Blowups

/-! Finite smooth-center sequences on compact integral ambient schemes can use integral centers throughout. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem Integral.CenterSequenceReplacement.Construction.exists_integral_sequence_of_smooth_center_continuation
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    (I : X.IdealSheafData) (hI : I ≠ ⊥) [Smooth (I.subschemeι ≫ f)]
    [NoetherianSpace I.subscheme] (b : ℕ) (hb : 0 < b) (hp : J ≤ I ^ b)
    (R : Global.MonomialSequence.Construction.SmoothFixedControlSequence b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b)) (hR : R.integralCenters) :
    ∃ S : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J, S.integralCenters := by
  let : Fintype (irreducibleComponents I.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype I
  let e := (Fintype.equivFin (irreducibleComponents I.subscheme)).symm
  let K (i : Fin (Fintype.card (irreducibleComponents I.subscheme))) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I (e i)
  have hprod : I = ∏ i, K i := by
    change I = ∏ i, Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I (e i)
    rw [e.prod_comp, Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_prod]
  exact Finite.CenterFactorSequence.Construction.exists_integral_sequence_of_finite_center_factorization _ X f J hJ b hb I hI K
    (fun i => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_ne_bot f I hI (e i))
    (fun i => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_integral f I (e i))
    (fun i => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_smooth f I (e i))
    (fun i j hij => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_sup f I (e i) (e j) (fun h => hij (e.injective h)))
    hprod inferInstance hp R hR

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.exists_integral_replacement
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J) [IsIntegral X] [IsLocallyNoetherian X]
    [CompactSpace X] [Smooth f] (hJ : J ≠ ⊥) :
    ∃ S : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J, S.integralCenters := by
  revert hJ
  revert ‹Smooth f› ‹CompactSpace X› ‹IsLocallyNoetherian X› ‹IsIntegral X›
  induction T with
  | @terminal Y g hs J ht =>
      intro _ _ _ _ _
      refine ⟨.terminal ht, ?_⟩
      change True
      trivial
  | @blowup Y hY hN g J I hI hb hp hs hbl tail ih =>
      intro _ _ hcompact hg hJ
      let : CompactSpace Y := hcompact
      let : Smooth g := hg
      let : Smooth (I.subschemeι ≫ g) := hs
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ g) := hbl
      let : CompactSpace (GlobalBlowup.Data.Construction.globalBlowup I hI) := QuasiCompact.compactSpace_of_compactSpace (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
      let : IsNoetherian Y := ⟨⟩
      let : NoetherianSpace I.subscheme := I.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
      obtain ⟨R, hR⟩ := ih (GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot I J hI b hJ)
      exact Integral.CenterSequenceReplacement.Construction.exists_integral_sequence_of_smooth_center_continuation g J hJ I hI b hb hp R hR

end AlgebraicGeometry.Resolution.Blowups

namespace AlgebraicGeometry.Resolution.Blowups.Integral.CenterSequenceReplacement.Construction

/-! Global boundary monomials on compact integral ambient schemes admit actual fixed-control sequences using integral centers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem boundaryMonomialSheaf_ne_bot
    {X : Scheme} [IsIntegral X] {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (a : β → ℕ) (hD : ∀ j, D j ≠ ⊥) :
    Global.MixedBoundary.Construction.boundaryMonomialSheaf D a ≠ ⊥ :=
  IdealSheafProducts.Construction.idealSheaf_finset_prod_ne_bot (fun j => D j ^ a j) Finset.univ
    (fun j _ => IdealSheafProducts.Construction.idealSheaf_pow_ne_bot (D j) (hD j) (a j))

theorem exists_global_boundary_monomial_integral_center_sequence
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (hD : ∀ j, D j ≠ ⊥)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) (a : β → ℕ) (b : ℕ) (hb : 0 < b) :
    ∃ T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a), T.integralCenters := by
  obtain ⟨T⟩ := Global.MonomialSequence.Construction.exists_global_boundary_monomial_sequence f D hD A a b hb
  exact T.exists_integral_replacement (boundaryMonomialSheaf_ne_bot D a hD)

end AlgebraicGeometry.Resolution.Blowups.Integral.CenterSequenceReplacement.Construction

end

end OAI
