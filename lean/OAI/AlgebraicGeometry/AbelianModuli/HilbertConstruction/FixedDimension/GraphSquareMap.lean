import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.SquareFiniteMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSectionGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphPolynomial

/-! # Graph Square Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The complete section system of the graph-bundle square gives a finite
map into projective space of dimension fixed by `g` and `δ`. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators
universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

def PolarizationData.PolarizedAbelianWithFullLevel.graphSquareSectionBasis (hg : 0 < g) (hδ : ∀ i, 0 < δ i)
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    Module.Basis (Fin (Graph.EmbeddingNumerics.graphSquareSectionRank g δ - 1 + 1)) K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj (A.graphBundle.tensorPower 2).sheaf) := by
  have := A.graphBundle_positivePower_sections_finite_overField 2
  apply Module.finBasisOfFinrankEq K _
  have he := A.graphBundle_positivePower_sections_finrank_normalized hg hN hNk 2 (by decide)
  change Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
    (A.graphBundle.tensorPower 2).sheaf) = Graph.EmbeddingNumerics.graphSquareSectionRank g δ at he
  exact he.trans (Nat.sub_add_cancel (Nat.succ_le_of_lt (Graph.EmbeddingNumerics.graphSquareSectionRank_pos g δ hδ))).symm

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_fixed_dimension_finite_square_map
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    ∃ (s : Fin (Graph.EmbeddingNumerics.graphSquareSectionRank g δ - 1 + 1) →
        (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower 2).sheaf))
      (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)),
      IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left ∧
      Nonempty (((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) (Graph.EmbeddingNumerics.graphSquareSectionRank g δ - 1)).pullback (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left).sheaf ≅
          (A.graphBundle.tensorPower 2).sheaf) := by
  let b := A.graphSquareSectionBasis hg hδ hN hNk
  let s := BasisSectionGeneration.sectionBasisFamily A.abelian.scheme.hom (A.graphBundle.tensorPower 2).sheaf b
  have hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i) :=
    BasisSectionGeneration.sectionBasisFamily_covers A.abelian.scheme.hom (A.graphBundle.tensorPower 2) b
      (A.graphBundle_square_pointwise_sections_overField hN hNk)
  exact ⟨s, hs, A.graphBundle_square_sectionMap_isFinite s hs,
    ⟨RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso A.abelian.scheme.hom s hs⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
