import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.StructureOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementParameterPullback

/-! # Structure Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower

noncomputable section

/-! Every actual tame full-level graph-power enhancement factors through
the structure-sheaf H1 bound open. The test scheme is arbitrary. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S] {g N : ℕ}
    {δ : Fin g → ℕ} (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (L : Line.Bundles.LineBundle F.abelian.scheme.left) (d : ℕ)
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    {T : Scheme.{u}} (b : T ⟶ S)
    (H : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback b)
      (L.pullback (CategoryTheory.Limits.pullback.fst F.abelian.scheme.hom b)) d)

include hN hunit H in
theorem PolarizationEnhancementData.GraphPowerPolarizationEnhancement.range_structureH1Open :
    Set.range b ⊆ (F.abelian.structureH1Open P g : Set S) := by
  rintro _ ⟨t, rfl⟩
  let K := T.residueField t
  let c : Spec (.of K) ⟶ T := T.fromSpecResidueField t
  let a : Over.mk (c ≫ b) ⟶ Over.mk b := Over.homMk c rfl
  let HK := H.parameterPullback a
  have hNK : (N : K) ≠ 0 := by
    have hu := (Abelian.Schemes.level_unit_under_base_change (c ≫ b) N hunit).map
      (Scheme.ΓSpecIso (.of K)).hom.hom
    simpa only [map_natCast] using hu.ne_zero
  have hr := F.abelian.structureH1Open_contains_polarized_fiber P
    (c ≫ b) HK.object (Iso.refl _) hN hNK
  let x : Spec (.of K) := (⊥ : PrimeSpectrum K)
  have hx := hr ⟨x, rfl⟩
  change b (T.fromSpecResidueField t x) ∈ (F.abelian.structureH1Open P g : Set S) at hx
  change b t ∈ (F.abelian.structureH1Open P g : Set S)
  simpa only [Scheme.fromSpecResidueField_apply] using hx

def PolarizationEnhancementData.GraphPowerPolarizationEnhancement.structureH1OpenLift : T ⟶ F.abelian.structureH1Open P g :=
  IsOpenImmersion.lift (F.abelian.structureH1Open P g).ι b (by
    simpa only [Scheme.Opens.range_ι] using
      PolarizationEnhancementData.GraphPowerPolarizationEnhancement.range_structureH1Open F P L d hN hunit b H)

theorem PolarizationEnhancementData.GraphPowerPolarizationEnhancement.structureH1OpenLift_ι :
    PolarizationEnhancementData.GraphPowerPolarizationEnhancement.structureH1OpenLift F P L d hN hunit b H ≫ (F.abelian.structureH1Open P g).ι = b :=
  IsOpenImmersion.lift_fac _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower
