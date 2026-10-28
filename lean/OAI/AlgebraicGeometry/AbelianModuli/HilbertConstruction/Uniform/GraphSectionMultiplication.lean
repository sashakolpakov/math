import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.GraphSquareMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SquareSectionMultiplicationSurjectivity

/-! # Graph Section Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The normalized square-section dimension supplies a uniform threshold
for multiplication of actual graph-bundle sections over every tame field. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped BigOperators
universe u
variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_square_multiplication_uniformly_surjective
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (q : ℕ) (hq : 2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ - 1 ≤ q) :
    ∀ t : Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower (2 + q)).sheaf,
      ∃ (n : ℕ)
        (s : Fin n → (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower 2).sheaf))
        (v : Fin n → (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower q).sheaf)),
        t = ∑ i, Tensor.ProductSections.tensorProductSection (s i) (v i) ≫ (A.graphBundle.tensorPowerAddIso 2 q).inv := by
  let r := Graph.EmbeddingNumerics.graphSquareSectionRank g δ
  have hr : 0 < r := Graph.EmbeddingNumerics.graphSquareSectionRank_pos g δ hδ
  let B := A.graphSquareSectionBasis hg hδ hN hNk
  let σ := BasisSectionGeneration.sectionBasisFamily A.abelian.scheme.hom (A.graphBundle.tensorPower 2).sheaf B
  let ss := List.ofFn σ
  have hlen : ss.length = r := by
    change (List.ofFn σ).length = r
    rw [List.length_ofFn]
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hr)
  have hcover : ∀ x : A.abelian.scheme.left, ∃ s ∈ ss, x ∈ Ample.LineBundles.sectionNonvanishing s := by
    intro x
    obtain ⟨i, hi⟩ := BasisSectionGeneration.sectionBasisFamily_covers A.abelian.scheme.hom (A.graphBundle.tensorPower 2) B
      (A.graphBundle_square_pointwise_sections_overField hN hNk) x
    exact ⟨σ i, List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩
  have hunit : IsUnit (N : Γ(Spec (.of K), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hNk).map (Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of K))))
  have hG : ∀ b : ℕ, 0 < b → ∀ i : ℕ,
      Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (A.graphBundle.tensorPower b).sheaf (i + 1)) :=
    fun b hb i => ModuleCat.isZero_iff_subsingleton.mp
      (A.graphBundle_positivePower_cohomology_vanishes_overField hN hunit b hb i)
  let b := q - (ss.length - 1) * 2
  have hb : 0 < b := by
    dsimp [b]
    rw [hlen]
    change 2 * r - 1 ≤ q at hq
    omega
  have heq : (ss.length - 1) * 2 + b = q := by
    dsimp [b]
    rw [hlen]
    change 2 * r - 1 ≤ q at hq
    omega
  have h := SquareSectionMultiplicationSurjectivity.lineBundleSquare_powerSections_products A.graphBundle hG ss hcover
    (by rw [hlen]; exact hr) b hb
  rw [heq] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
