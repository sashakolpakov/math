import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechTotal
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechRefinement

/-! # Smooth Cech Total Refinement -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechTotalRefinement

noncomputable section

/-!
# Cover refinement of the actual smooth Čech total complex

Totalizing the proved refinement morphism gives the ordinary restrictions
on each direct-sum summand. These maps compose and preserve the actual
de Rham augmentation.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {E ι κ ν : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (U : ι → Opens E) (V : κ → Opens E) (r : κ → ι) (hr : ∀ k, V k ≤ U (r k))

/-- The actual refinement map of signed smooth Čech–de Rham total complexes. -/
def smoothCechTotalRefinement : SmoothCechTotal.smoothCechTotal U ⟶ SmoothCechTotal.smoothCechTotal V :=
  HomologicalComplex₂.total.map (SmoothCechRefinement.smoothCechDoubleComplexRefinement U V r hr) (ComplexShape.up ℕ)

/-- On every total summand, refinement is the genuine restriction of forms. -/
theorem smoothCechTotalInclusion_refinement (n p k : ℕ) (h : n + p = k) :
    SmoothCechTotal.smoothCechTotalInclusion U n p k h ≫ (smoothCechTotalRefinement U V r hr).f k =
      ModuleCat.ofHom (SmoothCech.cechRefinementMap (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E p) U V r hr n) ≫
        SmoothCechTotal.smoothCechTotalInclusion V n p k h :=
  HomologicalComplex₂.ιTotal_map (K := SmoothCechDoubleComplex.smoothCechDoubleComplex U)
    (L := SmoothCechDoubleComplex.smoothCechDoubleComplex V) (φ := SmoothCechRefinement.smoothCechDoubleComplexRefinement U V r hr)
    (c₁₂ := ComplexShape.up ℕ) n p k h

/-- Identity refinement induces the identity map of actual total complexes. -/
theorem smoothCechTotalRefinement_id :
    smoothCechTotalRefinement U U id (fun _ => le_refl _) = 𝟙 (SmoothCechTotal.smoothCechTotal U) := by
  change HomologicalComplex₂.total.map
    (SmoothCechRefinement.smoothCechDoubleComplexRefinement U U id (fun _ => le_refl _)) (ComplexShape.up ℕ) = _
  rw [SmoothCechRefinement.smoothCechDoubleComplexRefinement_id, HomologicalComplex₂.total.map_id]
  rfl

/-- Successive cover refinements compose on the actual total complexes. -/
theorem smoothCechTotalRefinement_comp (W : ν → Opens E) (s : ν → κ)
    (hs : ∀ l, W l ≤ V (s l)) :
    smoothCechTotalRefinement U V r hr ≫ smoothCechTotalRefinement V W s hs =
      smoothCechTotalRefinement U W (r ∘ s) (fun l => (hs l).trans (hr (s l))) := by
  change HomologicalComplex₂.total.map (SmoothCechRefinement.smoothCechDoubleComplexRefinement U V r hr)
      (ComplexShape.up ℕ) ≫
    HomologicalComplex₂.total.map (SmoothCechRefinement.smoothCechDoubleComplexRefinement V W s hs)
      (ComplexShape.up ℕ) = _
  rw [← HomologicalComplex₂.total.map_comp, SmoothCechRefinement.smoothCechDoubleComplexRefinement_comp]
  rfl

/-- The actual augmentation to the total complex is natural under cover refinement. -/
theorem smoothCechAugmentationToTotal_refinement (W : Opens E) (hU : ∀ i, U i ≤ W) :
    SmoothCechTotal.smoothCechAugmentationToTotal U W hU ≫ smoothCechTotalRefinement U V r hr =
      SmoothCechTotal.smoothCechAugmentationToTotal V W (fun k => (hr k).trans (hU (r k))) := by
  apply HomologicalComplex.Hom.ext
  funext p
  let augU := (SmoothCechDoubleComplex.smoothCechColumnAugmentation U W hU).f p
  let augV := (SmoothCechDoubleComplex.smoothCechColumnAugmentation V W (fun k => (hr k).trans (hU (r k)))).f p
  let res := (SmoothCechRefinement.smoothCechColumnRefinement U V r hr 0).f p
  let iU := SmoothCechTotal.smoothCechTotalInclusion U 0 p p (Nat.zero_add p)
  let iV := SmoothCechTotal.smoothCechTotalInclusion V 0 p p (Nat.zero_add p)
  have hi : iU ≫ (smoothCechTotalRefinement U V r hr).f p = res ≫ iV :=
    smoothCechTotalInclusion_refinement U V r hr 0 p p (Nat.zero_add p)
  have ha : augU ≫ res = augV := congrArg (fun f => f.f p)
    (SmoothCechRefinement.smoothCechColumnAugmentation_refinement U V r hr W hU)
  change (augU ≫ iU) ≫ (smoothCechTotalRefinement U V r hr).f p = augV ≫ iV
  calc
    (augU ≫ iU) ≫ (smoothCechTotalRefinement U V r hr).f p =
        augU ≫ (iU ≫ (smoothCechTotalRefinement U V r hr).f p) := Category.assoc _ _ _
    _ = augU ≫ (res ≫ iV) := congrArg (fun f => augU ≫ f) hi
    _ = (augU ≫ res) ≫ iV := (Category.assoc _ _ _).symm
    _ = augV ≫ iV := congrArg (fun f => f ≫ iV) ha

/-- Global de Rham augmentation is independent of refining the chosen cover. -/
theorem smoothCechGlobalAugmentationToTotal_refinement :
    SmoothCechTotal.smoothCechGlobalAugmentationToTotal U ≫ smoothCechTotalRefinement U V r hr =
      SmoothCechTotal.smoothCechGlobalAugmentationToTotal V := by
  change (Analysis.DifferentialForms.Manifold.OpenDeRhamX.deRhamOnOpen ⊤ ≫ SmoothCechTotal.smoothCechAugmentationToTotal U ⊤ (fun _ => le_top)) ≫
    smoothCechTotalRefinement U V r hr =
      Analysis.DifferentialForms.Manifold.OpenDeRhamX.deRhamOnOpen ⊤ ≫ SmoothCechTotal.smoothCechAugmentationToTotal V ⊤ (fun _ => le_top)
  rw [Category.assoc, smoothCechAugmentationToTotal_refinement]

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechTotalRefinement
