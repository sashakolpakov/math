import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EvenGraphSectionFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphPowerBasis

/-! # Even Graph Power Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Complete section bases and finite projective maps for arbitrary
positive even powers of the canonical graph bundle. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def EvenGraphPowerBasis.evenGraphSectionRank (g : ℕ) (δ : Fin g → ℕ) (t : ℕ) : ℕ :=
  (2 : ℕ) ^ g * (∏ i, δ i) * (2 * t) ^ g

theorem EvenGraphPowerBasis.evenGraphSectionRank_pos (g : ℕ) (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)
    (t : ℕ) (ht : 0 < t) : 0 < EvenGraphPowerBasis.evenGraphSectionRank g δ t := by
  exact Nat.mul_pos (Nat.mul_pos (pow_pos (by decide) g) (Finset.prod_pos (fun i _ => hδ i)))
    (pow_pos (Nat.mul_pos (by decide) ht) g)

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
variable (t : ℕ) (ht : 0 < t)

def PolarizationData.PolarizedAbelianWithFullLevel.evenGraphPowerSectionBasis :
    Module.Basis (Fin (EvenGraphPowerBasis.evenGraphSectionRank g δ t - 1 + 1)) K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj (A.graphBundle.tensorPower (2 * t)).sheaf) := by
  have := A.graphBundle_positivePower_sections_finite_overField (2 * t)
  apply Module.finBasisOfFinrankEq K _
  have he := A.graphBundle_positivePower_sections_finrank_normalized hg hN hNk (2 * t)
    (Nat.mul_pos (by decide) ht)
  change Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
    (A.graphBundle.tensorPower (2 * t)).sheaf) = EvenGraphPowerBasis.evenGraphSectionRank g δ t at he
  exact he.trans (Nat.sub_add_cancel (Nat.succ_le_of_lt (EvenGraphPowerBasis.evenGraphSectionRank_pos g δ hδ t ht))).symm

include hN hNk ht in
theorem PolarizationData.PolarizedAbelianWithFullLevel.evenGraphPower_pointwise_sections :
    ∀ x : A.abelian.scheme.left, ∃ s : Line.Bundles.structureModule A.abelian.scheme.left ⟶
      (A.graphBundle.tensorPower (2 * t)).sheaf, x ∈ Ample.LineBundles.sectionNonvanishing s := by
  intro x
  obtain ⟨s, hs⟩ := A.graphBundle_square_pointwise_sections_overField hN hNk x
  let e : ((A.graphBundle.tensorPower 2).tensorPower t).sheaf ≅
      (A.graphBundle.tensorPower (2 * t)).sheaf :=
    (A.graphBundle.tensorPowerComposeIso t 2).symm ≪≫
      eqToIso (congrArg (fun d => (A.graphBundle.tensorPower d).sheaf) (Nat.mul_comm t 2))
  refine ⟨TensorPower.Maps.tensorPowerSection s t ≫ e.hom, ?_⟩
  erw [Ample.Powers.sectionNonvanishing_comp_iso, Section.PowerLocus.sectionNonvanishing_tensorPowerSection s t ht]
  exact hs

def PolarizationData.PolarizedAbelianWithFullLevel.evenGraphPowerSections : Fin (EvenGraphPowerBasis.evenGraphSectionRank g δ t - 1 + 1) →
    (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower (2 * t)).sheaf) :=
  BasisSectionGeneration.sectionBasisFamily A.abelian.scheme.hom (A.graphBundle.tensorPower (2 * t)).sheaf
    (A.evenGraphPowerSectionBasis hg hδ hN hNk t ht)

theorem PolarizationData.PolarizedAbelianWithFullLevel.evenGraphPowerSections_cover : ∀ x : A.abelian.scheme.left,
    ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (A.evenGraphPowerSections hg hδ hN hNk t ht i) :=
  BasisSectionGeneration.sectionBasisFamily_covers A.abelian.scheme.hom (A.graphBundle.tensorPower (2 * t))
    (A.evenGraphPowerSectionBasis hg hδ hN hNk t ht) (A.evenGraphPower_pointwise_sections hN hNk t ht)

theorem PolarizationData.PolarizedAbelianWithFullLevel.evenGraphPower_sectionMap_isFinite :
    IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom
      (A.evenGraphPowerSections hg hδ hN hNk t ht) (A.evenGraphPowerSections_cover hg hδ hN hNk t ht)).left := by
  apply GeometricallyAmpleSectionMorphism.sectionProjectiveMorphism_isFinite_of_geometric_ample A.abelian.scheme.hom
    (A.graphBundle.tensorPower (2 * t)) _ _
  intro F _ _ f
  exact ((A.graphBundle_ample_geometricFiber F f).tensorPower (2 * t) (Nat.mul_pos (by decide) ht)).of_iso
    (A.graphBundle.powerBaseChangeIso (CategoryTheory.Limits.pullback.fst A.abelian.scheme.hom f) (2 * t)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
