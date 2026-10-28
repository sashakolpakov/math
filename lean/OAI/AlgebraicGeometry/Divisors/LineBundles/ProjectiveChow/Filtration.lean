import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowPower
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChowReindex

/-! # Filtration -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.Filtration.BundleCycles

noncomputable section

section

/-! Actual projective Chow summands are iterated line-bundle
intersections of fiber extensions, in their genuine dimension grades. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)

def projectiveChowComponent (d k i : ℕ) (hd : k + r = d + i) :
    DimensionChow.BundleCycles.DimensionChowQ f k →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d :=
  (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) d i).comp
    ((DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl hd).toLinearMap.comp (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp k))

def projectiveChowGenerated (d : ℕ) : Submodule ℚ (DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) :=
  Submodule.span ℚ {a | ∃ (k i : ℕ), i ≤ r ∧ ∃ (hd : k + r = d + i) (β : DimensionChow.BundleCycles.DimensionChowQ f k),
    projectiveChowComponent p f r hp L d k i hd β = a}

theorem projectiveChowComponent_mem_generated (d k i : ℕ) (hi : i ≤ r) (hd : k + r = d + i)
    (β : DimensionChow.BundleCycles.DimensionChowQ f k) :
    projectiveChowComponent p f r hp L d k i hd β ∈ projectiveChowGenerated p f r hp L d :=
  Submodule.subset_span ⟨k, i, hi, hd, β, rfl⟩

theorem affineSpaceSourceChowExtension_mem_projectiveGenerated (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d α ∈ projectiveChowGenerated p f r hp L (d + r) :=
  projectiveChowComponent_mem_generated p f r hp L (d + r) d 0 (Nat.zero_le r) rfl α

end

/-! The actual projective Chow generators filtered by their
intersection exponent, with a constructive highest-exponent splitting. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)

def projectiveChowFiltration (d bound : ℕ) : Submodule ℚ (DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) :=
  Submodule.span ℚ {a | ∃ (k i : ℕ), i < bound ∧ ∃ (hd : k + r = d + i) (β : DimensionChow.BundleCycles.DimensionChowQ f k),
    projectiveChowComponent p f r hp L d k i hd β = a}

theorem projectiveChowFiltration_zero (d : ℕ) : projectiveChowFiltration p f r hp L d 0 = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro a ⟨k, i, hi, hd, β, rfl⟩
  omega

theorem projectiveChowFiltration_full (d : ℕ) :
    projectiveChowFiltration p f r hp L d (r + 1) = projectiveChowGenerated p f r hp L d := by
  unfold projectiveChowFiltration projectiveChowGenerated
  simp only [Nat.lt_succ_iff]

theorem projectiveChowFiltration_below_rank (d m : ℕ) (hd : d + m < r) :
    projectiveChowFiltration p f r hp L d (m + 1) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro a ⟨k, i, hi, hki, β, rfl⟩
  omega

theorem projectiveChowFiltration_split (d m k : ℕ) (hk : k + r = d + m)
    (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) (hα : α ∈ projectiveChowFiltration p f r hp L d (m + 1)) :
    ∃ γ : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d, γ ∈ projectiveChowFiltration p f r hp L d m ∧
      ∃ β : DimensionChow.BundleCycles.DimensionChowQ f k, α = γ + projectiveChowComponent p f r hp L d k m hk β := by
  induction hα using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, i, hi, hli, β, rfl⟩ := ha
    by_cases him : i < m
    · refine ⟨_, Submodule.subset_span ⟨l, i, him, hli, β, rfl⟩, 0, ?_⟩
      rw [map_zero, add_zero]
    · have he : i = m := by omega
      subst i
      have hl : l = k := by omega
      subst l
      exact ⟨0, Submodule.zero_mem _, β, by rw [zero_add]⟩
  | zero => exact ⟨0, Submodule.zero_mem _, 0, by rw [map_zero, add_zero]⟩
  | add a b ha hb ia ib =>
    obtain ⟨γ, hγ, β, eβ⟩ := ia
    obtain ⟨δ, hδ, ε, eε⟩ := ib
    refine ⟨γ + δ, Submodule.add_mem _ hγ hδ, β + ε, ?_⟩
    rw [map_add, eβ, eε]
    abel
  | smul c a ha ia =>
    obtain ⟨γ, hγ, β, eβ⟩ := ia
    exact ⟨c • γ, Submodule.smul_mem _ c hγ, c • β, by rw [map_smul, eβ, smul_add]⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.Filtration.BundleCycles
