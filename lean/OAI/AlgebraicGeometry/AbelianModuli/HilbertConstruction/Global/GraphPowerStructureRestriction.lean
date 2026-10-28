import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.StructureOpen

/-! # Graph Power Structure Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Original graph-power enhancements on arbitrary tests factor through
the global first-cohomology bound open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ}
    {δ : Fin g → ℕ} (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (L : Line.Bundles.LineBundle F.abelian.scheme.left) (d : ℕ)
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    {T : Scheme.{u}} (b : T ⟶ S)
    (H : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback b)
      (L.pullback (pullback.fst F.abelian.scheme.hom b)) d)

include hN hunit H in
theorem GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.range_globalStructureH1Open :
    Set.range b ⊆ (F.abelian.globalStructureH1Open P g : Set S) := by
  rintro _ ⟨t, rfl⟩
  let K := T.residueField t
  let c : Spec (.of K) ⟶ T := T.fromSpecResidueField t
  let a : Over.mk (c ≫ b) ⟶ Over.mk b := Over.homMk c rfl
  let HK := H.parameterPullback a
  have hNK : (N : K) ≠ 0 := by
    have hu := (Abelian.Schemes.level_unit_under_base_change (c ≫ b) N hunit).map
      (Scheme.ΓSpecIso (.of K)).hom.hom
    simpa only [map_natCast] using hu.ne_zero
  have hr := F.abelian.globalStructureH1Open_contains_polarized_fiber P
    (c ≫ b) HK.object (Iso.refl _) hN hNK
  let x : Spec (.of K) := (⊥ : PrimeSpectrum K)
  have hx := hr (Set.mem_range_self x)
  change b (T.fromSpecResidueField t x) ∈ (F.abelian.globalStructureH1Open P g : Set S) at hx
  change b t ∈ (F.abelian.globalStructureH1Open P g : Set S)
  simpa only [Scheme.fromSpecResidueField_apply] using hx

def GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.globalStructureH1OpenLift : T ⟶ F.abelian.globalStructureH1Open P g :=
  IsOpenImmersion.lift (F.abelian.globalStructureH1Open P g).ι b (by
    simpa only [Scheme.Opens.range_ι] using
      GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.range_globalStructureH1Open F P L d hN hunit b H)

theorem GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.globalStructureH1OpenLift_ι :
    GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.globalStructureH1OpenLift F P L d hN hunit b H ≫
      (F.abelian.globalStructureH1Open P g).ι = b :=
  IsOpenImmersion.lift_fac _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
