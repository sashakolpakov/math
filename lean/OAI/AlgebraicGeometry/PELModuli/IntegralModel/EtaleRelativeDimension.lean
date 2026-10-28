import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DimensionUniqueness
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Etale Relative Dimension -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.EtaleRelativeDimension.DimensionSupport

noncomputable section

/-! Smooth relative dimension descends through a surjective étale map.
The proof compares the dimensions of the actual pulled-back affine
charts, without adding any dimension-identification premise. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem smooth_relative_dimension_of_etale_cover
    {X Y S : Scheme} (q : X ⟶ Y) [Etale q] [Surjective q]
    (f : Y ⟶ S) [Smooth f] (n : ℕ) [SmoothOfRelativeDimension n (q ≫ f)] :
    SmoothOfRelativeDimension n f := by
  constructor
  intro y
  obtain ⟨U, hU, V, hV, hy, e, hstd⟩ := Smooth.exists_isStandardSmooth f y
  let : Algebra Γ(S, U) Γ(Y, V) := (f.appLE U V e).hom.toAlgebra
  change Algebra.IsStandardSmooth Γ(S, U) Γ(Y, V) at hstd
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hstd
  let := hσ
  let := hι
  have hP := P.isStandardSmoothOfRelativeDimension rfl
  have hchart : SmoothOfRelativeDimension P.dimension (f.resLE U V e) :=
    SmoothDimensionCharts.DimensionSupport.smoothOfRelativeDimension_resLE_of_appLE f P.dimension U V hU hV e hP
  have hVdim : SmoothOfRelativeDimension P.dimension (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    exact inferInstanceAs (SmoothOfRelativeDimension (P.dimension + 0) (f.resLE U V e ≫ U.ι))
  let Z := pullback q V.ι
  let p : Z ⟶ S := pullback.fst q V.ι ≫ (q ≫ f)
  have hpn : SmoothOfRelativeDimension n p := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (pullback.fst q V.ι ≫ (q ≫ f)))
  have hpm : SmoothOfRelativeDimension P.dimension p := by
    have hp : p = pullback.snd q V.ι ≫ (V.ι ≫ f) := by
      dsimp only [p]
      rw [← Category.assoc, pullback.condition, Category.assoc]
    rw [hp]
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + P.dimension)
        (pullback.snd q V.ι ≫ (V.ι ≫ f)))
  have : Nonempty Z := by
    obtain ⟨z, _⟩ := (pullback.snd q V.ι).surjective (⟨y, hy⟩ : V.toScheme)
    exact ⟨z⟩
  have hd : P.dimension = n := Relative.DimensionUniqueness.DimensionSupport.smooth_relative_dimension_unique p P.dimension n
  refine ⟨U, hU, V, hV, hy, e, ?_⟩
  exact hd ▸ hP

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.EtaleRelativeDimension.DimensionSupport
