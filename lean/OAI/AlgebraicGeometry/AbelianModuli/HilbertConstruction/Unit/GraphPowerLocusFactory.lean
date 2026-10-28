import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.GlobalGraphPowerParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.GraphPowerStructureRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.TranslationKernelOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.ProjectiveRestriction

/-! # Graph Power Locus Factory -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.GraphPowerLocusFactory

noncomputable section

/-! The arithmetic graph-power locus for the original full-level family.
The auxiliary first-cohomology and unramified-kernel opens contain every
original enhancement, including enhancements over nonreduced tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem unitGraphPowerLocus_nonempty
    {R : Type} [CommRing R]
    (M : Over (Spec (.of R))) [IsNoetherian M.left] {g N : ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N M.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)
    (hN : 3 ≤ N) (hunitN : IsUnit (N : Γ(M.left, ⊤)))
    (hunit : IsUnit ((2 * d : ℕ) : Γ(M.left, ⊤))) :
    Nonempty (GraphPower.LocusPresentation.GraphPowerLocusPresentation M F P d δ) := by
  classical
  let U := F.abelian.globalStructureH1Open P g ⊓
    TranslationKernelUnramifiedOpen.translationKernelUnramifiedOpen F.abelian P.ampleLineBundle P
  let i := U.ι
  let V : Over (Spec (.of R)) := Over.mk (i ≫ M.hom)
  let j : V ⟶ M := Over.homMk i rfl
  let A := F.abelian.pullback i
  let F' := F.pullback i
  let P' := P.baseChange i
  let : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion i
  let : TopologicalSpace.NoetherianSpace M.left := IsNoetherian.noetherianSpace
  let : TopologicalSpace.NoetherianSpace U :=
    TopologicalSpace.NoetherianSpace.set (U : Set M.left)
  let : CompactSpace U := TopologicalSpace.NoetherianSpace.compactSpace U
  let hU : IsNoetherian U := ⟨⟩
  let : IsNoetherian V.left := hU
  have hHrange : Set.range i ⊆ (F.abelian.globalStructureH1Open P g : Set M.left) := by
    rw [Scheme.Opens.range_ι]
    exact fun _ hx => hx.1
  have hKrange : Set.range i ⊆ TranslationKernelUnramifiedOpen.translationKernelUnramifiedOpen F.abelian P.ampleLineBundle P := by
    rw [Scheme.Opens.range_ι]
    exact fun _ hx => hx.2
  have hH1 : A.HasFieldStructureH1Bound := by
    intro K _ b
    exact F.abelian.globalStructureH1Bound_of_range_subset P g i hHrange b
  have hK : FormallyUnramified (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A P'.ampleLineBundle P').hom :=
    TranslationKernelUnramifiedOpen.projectiveTranslationKernel_unramified_of_range_subset F.abelian P i hKrange
  obtain ⟨D⟩ := GlobalGraphPowerParameter.unitGlobalGraphPowerLocus_nonempty V F' P' hH1 hK d hd δ hδ
    (Abelian.Schemes.level_unit_under_base_change i (2 * d) hunit)
  let : Mono j.left := inferInstanceAs (Mono i)
  let : LocallyOfFiniteType j.left := inferInstanceAs (LocallyOfFiniteType i)
  let : QuasiCompact j.left := inferInstanceAs (QuasiCompact i)
  let : Mono D.inclusion.left := D.inclusion_left_mono
  let : LocallyOfFiniteType D.inclusion.left := D.inclusion_locallyOfFiniteType
  let : QuasiCompact D.inclusion.left := D.inclusion_quasiCompact
  refine ⟨{
    parameter := D.parameter
    inclusion := D.inclusion ≫ j
    inclusion_left_mono := inferInstanceAs (Mono (D.inclusion.left ≫ j.left))
    inclusion_locallyOfFiniteType :=
      inferInstanceAs (LocallyOfFiniteType (D.inclusion.left ≫ j.left))
    inclusion_quasiCompact := inferInstanceAs (QuasiCompact (D.inclusion.left ≫ j.left))
    lifts_iff := ?_
  }⟩
  intro T x
  constructor
  · rintro ⟨z, hz⟩
    let y := z ≫ D.inclusion
    have h := (D.lifts_iff T y).mp ⟨z, rfl⟩
    have hy : y ≫ j = x := (Category.assoc z D.inclusion j).trans hz
    have he : y.left ≫ i = x.left := congrArg Over.Hom.left hy
    have h' := (GraphPower.ProjectiveRestriction.projectiveGraphPowerEnhancement_baseChange_comp_iff δ F P d i y.left).mpr h
    exact he ▸ h'
  · rintro ⟨H⟩
    have hHr := GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.range_globalStructureH1Open
      F P (F.abelian.zeroNormalizedBundle P.ampleLineBundle) d hN hunitN x.left H
    have hKr := GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.range_translationKernelUnramifiedOpen
      F P P.ampleLineBundle d hδ hunit x.left H
    have hUr : Set.range x.left ⊆ Set.range i := by
      rw [Scheme.Opens.range_ι]
      exact fun _ hx => ⟨hHr hx, hKr hx⟩
    let a := IsOpenImmersion.lift i x.left hUr
    have ha : a ≫ i = x.left := IsOpenImmersion.lift_fac i x.left hUr
    let y : T ⟶ V := Over.homMk a (by
      change a ≫ (i ≫ M.hom) = T.hom
      rw [← Category.assoc, ha]
      exact x.w)
    have hy : y ≫ j = x := Over.OverMorphism.ext ha
    have h' : Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback (a ≫ i))
        ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
          (pullback.fst F.abelian.scheme.hom (a ≫ i))) d) := ha.symm ▸ ⟨H⟩
    have h'' := (GraphPower.ProjectiveRestriction.projectiveGraphPowerEnhancement_baseChange_comp_iff δ F P d i a).mp h'
    obtain ⟨z, hz⟩ := (D.lifts_iff T y).mpr h''
    exact ⟨z, (Category.assoc z D.inclusion j).symm.trans
      ((congrArg (fun t => t ≫ j) hz).trans hy)⟩

def unitGraphPowerLocusFactory
    (R : Type) [CommRing R] (g N d : ℕ) (δ : Fin g → ℕ)
    (hd : 0 < d) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hunitN : IsUnit (N : R)) (hunit : IsUnit ((2 * d : ℕ) : R)) :
    GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ := by
  have hNspec : IsUnit (N : Γ(Spec (.of R), ⊤)) := by
    simpa only [map_natCast] using hunitN.map (Scheme.ΓSpecIso (.of R)).inv.hom
  have hdspec : IsUnit ((2 * d : ℕ) : Γ(Spec (.of R), ⊤)) := by
    simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of R)).inv.hom
  intro M _ F P
  exact Classical.choice (unitGraphPowerLocus_nonempty M F P d hd δ hδ hN
    (Abelian.Schemes.level_unit_under_base_change M.hom N hNspec)
    (Abelian.Schemes.level_unit_under_base_change M.hom (2 * d) hdspec))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.GraphPowerLocusFactory
