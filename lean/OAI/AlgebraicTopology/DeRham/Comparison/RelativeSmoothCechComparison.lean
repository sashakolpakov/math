import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechComparison
import OAI.AlgebraicTopology.DeRham.Comparison.RelativeSmoothCech
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechTotalRefinement

/-! # Relative Smooth Cech Comparison -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RelativeSmoothCechComparison

noncomputable section

/-!
# Smooth Čech–de Rham comparison for arbitrary covers of an open domain

The relative smooth partition construction gives exactness without assuming
that the cover is finite. Together with actual smooth gluing, it proves that
the restriction augmentation from an open domain to its smooth Čech total
complex is a quasi-isomorphism.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {E ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable (W : Opens E) (U : ι → Opens E) (hsub : ∀ i, U i ≤ W)
variable (hcover : ∀ x : W, ∃ i, (x : E) ∈ U i)

include hsub hcover

/-- Relative partitions prove categorical row exactness for arbitrary open covers. -/
theorem relativeSmoothCechRow_exactAt (p q : ℕ) :
    ((SmoothCechDoubleComplex.smoothCechDoubleComplex U).flip.X q).ExactAt (p + 1) := by
  rw [SmoothCechDoubleComplex.smoothCechDoubleComplex_row]
  apply ((SmoothCech.smoothCechComplex U q).exactAt_iff' p (p + 1) (p + 2)
    (by simp) (by simp)).2
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
  change LinearMap.range (((SmoothCech.smoothCechComplex U q).d p (p + 1)).hom) =
    LinearMap.ker (((SmoothCech.smoothCechComplex U q).d (p + 1) (p + 2)).hom)
  rw [SmoothCech.cechComplex_d, SmoothCech.cechComplex_d]
  exact RelativeSmoothCech.smoothCechDelta_range_eq_ker_of_open_cover W U q hsub hcover p

/-- Actual smooth forms on an open domain compute the smooth Čech total
cohomology for every open cover of that domain. -/
theorem relativeSmoothCechAugmentation_quasiIso :
    QuasiIso (SmoothCechTotal.smoothCechAugmentationToTotal U W hsub) := by
  unfold SmoothCechTotal.smoothCechAugmentationToTotal
  apply DoubleComplexComparison.DoubleComplex.augmentationToTotal_quasiIso
  · intro q
    exact SmoothCechComparison.smoothCechColumnAugmentation_injective U W hsub
      (fun x hx => Set.mem_iUnion.mpr (hcover ⟨x, hx⟩)) q
  · intro q
    exact SmoothCechComparison.smoothCechColumnAugmentation_exact U W hsub
      (fun x hx => Set.mem_iUnion.mpr (hcover ⟨x, hx⟩)) q
  · intro p q
    exact relativeSmoothCechRow_exactAt W U hsub hcover p q

/-- The canonical comparison on cohomology is induced by the actual restriction map. -/
def relativeSmoothCechCohomologyIso (n : ℕ) :
    Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamCohomology W n ≅ (SmoothCechTotal.smoothCechTotal U).homology n := by
  letI : QuasiIso (SmoothCechTotal.smoothCechAugmentationToTotal U W hsub) :=
    relativeSmoothCechAugmentation_quasiIso W U hsub hcover
  exact isoOfQuasiIsoAt (SmoothCechTotal.smoothCechAugmentationToTotal U W hsub) n

@[simp]
theorem relativeSmoothCechCohomologyIso_hom (n : ℕ) :
    (relativeSmoothCechCohomologyIso W U hsub hcover n).hom =
      HomologicalComplex.homologyMap (SmoothCechTotal.smoothCechAugmentationToTotal U W hsub) n := rfl

omit W hsub hcover in
/-- The whole-domain augmentation works for arbitrary covers of the ambient space. -/
theorem smoothCechAugmentationToTotal_quasiIso_of_arbitrary_cover
    (hU : ∀ x : E, ∃ i, x ∈ U i) :
    QuasiIso (SmoothCechTotal.smoothCechAugmentationToTotal U ⊤ (fun _ => le_top)) :=
  relativeSmoothCechAugmentation_quasiIso ⊤ U (fun _ => le_top) (fun x => hU x)

omit W hsub hcover in
/-- Genuine global de Rham forms compute the smooth total cohomology of any open cover. -/
theorem smoothCechGlobalAugmentationToTotal_quasiIso_of_arbitrary_cover
    (hU : ∀ x : E, ∃ i, x ∈ U i) :
    QuasiIso (SmoothCechTotal.smoothCechGlobalAugmentationToTotal U) := by
  let : IsIso (Analysis.DifferentialForms.Manifold.OpenDeRhamX.deRhamOnOpen (⊤ : Opens E)) :=
    inferInstanceAs (IsIso (Analysis.DifferentialForms.Manifold.GlobalOpen.deRhamTopIso E).hom)
  let : QuasiIso (SmoothCechTotal.smoothCechAugmentationToTotal U ⊤ (fun _ => le_top)) :=
    smoothCechAugmentationToTotal_quasiIso_of_arbitrary_cover U hU
  change QuasiIso (Analysis.DifferentialForms.Manifold.OpenDeRhamX.deRhamOnOpen ⊤ ≫ SmoothCechTotal.smoothCechAugmentationToTotal U ⊤ (fun _ => le_top))
  infer_instance

omit W hsub hcover in
/-- The corresponding canonical global cohomology isomorphism for an arbitrary cover. -/
def smoothCechDeRhamCohomologyIso_of_arbitrary_cover
    (hU : ∀ x : E, ∃ i, x ∈ U i) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.DeRham.deRhamCohomology E n ≅ (SmoothCechTotal.smoothCechTotal U).homology n := by
  letI : QuasiIso (SmoothCechTotal.smoothCechGlobalAugmentationToTotal U) :=
    smoothCechGlobalAugmentationToTotal_quasiIso_of_arbitrary_cover U hU
  exact isoOfQuasiIsoAt (SmoothCechTotal.smoothCechGlobalAugmentationToTotal U) n

variable {κ : Type u} (V : κ → Opens E) (r : κ → ι)
variable (hr : ∀ k, V k ≤ U (r k)) (hV : ∀ x : W, ∃ k, (x : E) ∈ V k)

include hV

/-- A genuine refinement between two covers of the same open domain preserves total cohomology. -/
theorem relativeSmoothCechTotalRefinement_quasiIso :
    QuasiIso (SmoothCechTotalRefinement.smoothCechTotalRefinement U V r hr) := by
  let : QuasiIso (SmoothCechTotal.smoothCechAugmentationToTotal U W hsub) :=
    relativeSmoothCechAugmentation_quasiIso W U hsub hcover
  let : QuasiIso (SmoothCechTotal.smoothCechAugmentationToTotal U W hsub ≫
      SmoothCechTotalRefinement.smoothCechTotalRefinement U V r hr) := by
    rw [SmoothCechTotalRefinement.smoothCechAugmentationToTotal_refinement]
    exact relativeSmoothCechAugmentation_quasiIso W V (fun k => (hr k).trans (hsub (r k))) hV
  exact quasiIso_of_comp_left (SmoothCechTotal.smoothCechAugmentationToTotal U W hsub)
    (SmoothCechTotalRefinement.smoothCechTotalRefinement U V r hr)

/-- The cohomology isomorphism of a refinement is induced by actual restriction of forms. -/
def relativeSmoothCechRefinementCohomologyIso (n : ℕ) :
    (SmoothCechTotal.smoothCechTotal U).homology n ≅ (SmoothCechTotal.smoothCechTotal V).homology n := by
  letI : QuasiIso (SmoothCechTotalRefinement.smoothCechTotalRefinement U V r hr) :=
    relativeSmoothCechTotalRefinement_quasiIso W U hsub hcover V r hr hV
  exact isoOfQuasiIsoAt (SmoothCechTotalRefinement.smoothCechTotalRefinement U V r hr) n

end

end OAI.AlgebraicTopology.DeRham.Comparison.RelativeSmoothCechComparison
