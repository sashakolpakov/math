import OAI.AlgebraicTopology.Products.CompactSupportCap

/-! # Locally Finite Cap Truncation -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

/-!
# Compact traces of the actual locally finite cap product

Near a compact set, a spatially locally finite chain has the same coefficients
as its genuine finite truncation. The Alexander--Whitney cap operation preserves
this agreement. The results below compare actual coefficients and finite chains;
they do not assert that restriction to point germs detects homology classes.
-/

open _root_.CategoryTheory Set
open scoped Simplicial
open OAI.AlgebraicTopology.Products.CompactSupportCap

section

variable {R X ι κ : Type*} [CommRing R] [TopologicalSpace X]

/-- A spatially local operation preserves agreement on every image meeting an
arbitrary set. No compactness or local-contractibility hypothesis is needed. -/
theorem LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal.agrees_near
    {imageA : ι → Set X} {imageB : κ → Set X}
    {F : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R imageB}
    (hF : LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal F) (K : Set X)
    (a b : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA)
    (hab : ∀ i, (imageA i ∩ K).Nonempty → a i = b i)
    (j : κ) (hj : (imageB j ∩ K).Nonempty) :
    F a j = F b j := by
  obtain ⟨x, hxj, hxK⟩ := hj
  exact hF x a b (fun i hxi => hab i ⟨x, hxi, hxK⟩) j hxj

end

variable {R : Type} [CommRing R]

/-- The actual locally finite cap product only uses input coefficients near
the image of its output simplex. -/
theorem LocallyFiniteCapTruncation.Cycles.locallyFiniteCap_agrees_of_agrees
    (X : TopCat.{0}) (K : Set X) (p q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (a b : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q))
    (hab : ∀ σ, (LocallyFiniteChains.Cycles.singularSimplexImage X (p + q) σ ∩ K).Nonempty → a σ = b σ)
    (τ : (TopCat.toSSet.obj X) _⦋q⦌)
    (hτ : (LocallyFiniteChains.Cycles.singularSimplexImage X q τ ∩ K).Nonempty) :
    LocallyFiniteCap.Cycles.locallyFiniteCap X p q c a τ = LocallyFiniteCap.Cycles.locallyFiniteCap X p q c b τ :=
  (LocallyFiniteCap.Cycles.locallyFiniteCapLinear_isSpatiallyLocal X p q c).agrees_near K a b hab τ hτ

/-- On an output simplex meeting a compact set, locally finite cap is exactly
ordinary cap of the finite input truncation. -/
theorem LocallyFiniteCapTruncation.Cycles.locallyFiniteCap_truncation_agrees
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (p q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q))
    (τ : (TopCat.toSSet.obj X) _⦋q⦌)
    (hτ : (LocallyFiniteChains.Cycles.singularSimplexImage X q τ ∩ K).Nonempty) :
    LocallyFiniteCap.Cycles.locallyFiniteCap X p q c z τ =
      LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X q
        (AlgebraicTopology.Products.Cap.singularCap X p q c (AlgebraicTopology.Products.CompactSupportCap.compactSingularTruncation X K hK (p + q) z)) τ := by
  have hnear : ∀ σ, (LocallyFiniteChains.Cycles.singularSimplexImage X (p + q) σ ∩ K).Nonempty →
      z σ = LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X (p + q)
        (AlgebraicTopology.Products.CompactSupportCap.compactSingularTruncation X K hK (p + q) z) σ := by
    intro σ hσ
    rw [AlgebraicTopology.Products.CompactSupportCap.ordinaryToLocallyFinite_compactSingularTruncation]
    change z σ = LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation
      (LocallyFiniteChains.Cycles.singularSimplexImage X (p + q)) K hK z σ
    exact (LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation_agrees _ K hK z σ hσ).symm
  have h := LocallyFiniteCapTruncation.Cycles.locallyFiniteCap_agrees_of_agrees X K p q c z
    (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X (p + q)
      (AlgebraicTopology.Products.CompactSupportCap.compactSingularTruncation X K hK (p + q) z)) hnear τ hτ
  rw [LocallyFiniteCap.Cycles.locallyFiniteCap_ordinary] at h
  exact h

/-- Truncating the output coefficients gives the same actual finite family
whether cap is computed before or after finite input truncation. -/
theorem LocallyFiniteCapTruncation.Cycles.compactTruncation_locallyFiniteCap
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (p q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q)) :
    LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation (LocallyFiniteChains.Cycles.singularSimplexImage X q) K hK
        (LocallyFiniteCap.Cycles.locallyFiniteCap X p q c z) =
      LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation (LocallyFiniteChains.Cycles.singularSimplexImage X q) K hK
        (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X q
          (AlgebraicTopology.Products.Cap.singularCap X p q c (AlgebraicTopology.Products.CompactSupportCap.compactSingularTruncation X K hK (p + q) z))) := by
  classical
  apply Finsupp.ext
  intro τ
  simp only [LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation_apply]
  by_cases hτ : (LocallyFiniteChains.Cycles.singularSimplexImage X q τ ∩ K).Nonempty
  · simp only [ite_eq_left hτ]
    exact LocallyFiniteCapTruncation.Cycles.locallyFiniteCap_truncation_agrees X K hK p q c z τ hτ
  · simp only [ite_eq_right hτ]

/-- The preceding coefficient equality is also an equality of genuine
ordinary singular chains after compact output truncation. -/
theorem LocallyFiniteCapTruncation.Cycles.compactSingularTruncation_locallyFiniteCap
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (p q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q)) :
    AlgebraicTopology.Products.CompactSupportCap.compactSingularTruncation X K hK q (LocallyFiniteCap.Cycles.locallyFiniteCap X p q c z) =
      AlgebraicTopology.Products.CompactSupportCap.compactSingularTruncation X K hK q
        (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X q
          (AlgebraicTopology.Products.Cap.singularCap X p q c (AlgebraicTopology.Products.CompactSupportCap.compactSingularTruncation X K hK (p + q) z))) := by
  exact congrArg (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X q).symm
    (LocallyFiniteCapTruncation.Cycles.compactTruncation_locallyFiniteCap X K hK p q c z)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric
