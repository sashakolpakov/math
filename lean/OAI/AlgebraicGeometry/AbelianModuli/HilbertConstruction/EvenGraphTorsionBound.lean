import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EvenGraphPowerBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FactorizationBasisEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.PowerTorsionHyperplaneBound

/-! # Even Graph Torsion Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A uniform torsion bound for sections of every sufficiently large
even graph power. The coefficient is explicit in dimension, type, and power. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def EvenGraphTorsionBound.evenGraphTorsionDegree (g : ℕ) (δ : Fin g → ℕ) (t : ℕ) : ℕ :=
  EvenGraphPowerBasis.evenGraphSectionRank g δ t * g.factorial

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
variable (t : ℕ) (ht : 0 < t)

theorem PolarizationData.PolarizedAbelianWithFullLevel.evenGraphPowerSections_ratios_generate (htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t) :
    Section.ProjectivePresentation.SectionRatiosGenerate A.abelian.scheme.hom (A.evenGraphPowerSections hg hδ hN hNk t ht) := by
  have : CompactSpace A.abelian.scheme.left := QuasiCompact.compactSpace_of_compactSpace A.abelian.scheme.hom
  have : A.abelian.scheme.left.IsSeparated := ⟨by
    rw [← terminal.comp_from A.abelian.scheme.hom]; infer_instance⟩
  apply Power.FactorizationBasisEmbedding.sectionBasisFamily_ratios_generate A.abelian.scheme.hom (A.graphBundle.tensorPower (2 * t))
    (A.evenGraphPowerSectionBasis hg hδ hN hNk t ht)
  intro m hm
  simpa only [Nat.add_comm 1 m] using
    A.graphBundle_large_even_consecutive_sections_factor hg hδ hN hNk t htlarge m hm

theorem PolarizationData.PolarizedAbelianWithFullLevel.evenGraphPowerSections_affine (i : Fin (EvenGraphPowerBasis.evenGraphSectionRank g δ t - 1 + 1)) :
    IsAffineOpen (Ample.LineBundles.sectionNonvanishing (A.evenGraphPowerSections hg hδ hN hNk t ht i)) := by
  let p := A.abelian.scheme.hom
  let s := A.evenGraphPowerSections hg hδ hN hNk t ht
  let hs := A.evenGraphPowerSections_cover hg hδ hN hNk t ht
  let a := SectionsProjectiveMorphism.sectionAbsoluteMorphism p s hs
  let q := pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(Spec (.of K), ⊤)
    (EvenGraphPowerBasis.evenGraphSectionRank g δ t - 1)).hom (Spec (.of K)).toSpecΓ
  have : IsIso q := inferInstance
  have he : (SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).left ≫ q = a := pullback.lift_fst _ _ _
  have : IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).left :=
    A.evenGraphPower_sectionMap_isFinite hg hδ hN hNk t ht
  have : IsFinite q := inferInstance
  have : IsFinite a := he ▸ (MorphismProperty.comp_mem (@IsFinite)
    (SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).left q inferInstance inferInstance)
  have h := (StandardProjectiveCharts.standardProjectiveChart_isAffine Γ(Spec (.of K), ⊤)
    (EvenGraphPowerBasis.evenGraphSectionRank g δ t - 1) i).preimage a
  erw [ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage] at h
  exact h

include hg hN hNk ht in
theorem PolarizationData.PolarizedAbelianWithFullLevel.evenGraphPower_euler_eq_sectionRank :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower (2 * t)).sheaf =
      (EvenGraphPowerBasis.evenGraphSectionRank g δ t : ℤ) := by
  have hunit : IsUnit (N : Γ(Spec (.of K), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hNk).map (Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of K))))
  rw [A.graphBundle_positivePower_euler_eq_sections hN hunit (2 * t) (Nat.mul_pos (by decide) ht)]
  exact congrArg (fun n : ℕ => (n : ℤ))
    (A.graphBundle_positivePower_sections_finrank_normalized hg hN hNk (2 * t) (Nat.mul_pos (by decide) ht))

include hg hδ hN hNk ht in
theorem PolarizationData.PolarizedAbelianWithFullLevel.evenGraphPower_torsion_section_card_le [IsAlgClosed K]
    (htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t) (n : ℕ) (hn : 0 < n) (level : A.abelian.FullLevel n)
    (a : Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower (2 * t)).sheaf) (ha : a ≠ 0)
    {κ : Type v} [Finite κ] (x : κ → A.abelian.scheme.left) (hx : Function.Injective x)
    (hxa : ∀ i, x i ∉ Ample.LineBundles.sectionNonvanishing a)
    (hxn : ∀ i, (A.abelian.multiplication n).left (x i) =
      η[A.abelian.scheme].left (IsLocalRing.closedPoint K)) :
    Nat.card κ ≤ EvenGraphTorsionBound.evenGraphTorsionDegree g δ t * n ^ (2 * g - 2) := by
  cases g with
  | zero => omega
  | succ g =>
    have h := A.graphBundlePower_torsion_hyperplane_card_le hN hNk (2 * t)
      (A.evenGraphPowerSections hg hδ hN hNk t ht)
      (A.evenGraphPowerSections_cover hg hδ hN hNk t ht)
      (A.evenGraphPowerSections_affine hg hδ hN hNk t ht)
      (A.evenGraphPowerSections_ratios_generate hg hδ hN hNk t ht htlarge)
      n hn level a ha x hx hxa hxn
    rw [A.evenGraphPower_euler_eq_sectionRank hg hN hNk t ht] at h
    change Nat.card κ ≤ (EvenGraphPowerBasis.evenGraphSectionRank (g + 1) δ t * (g + 1).factorial) * n ^ (2 * (g + 1) - 2)
    rw [show 2 * (g + 1) - 2 = 2 * g by omega]
    exact_mod_cast h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
