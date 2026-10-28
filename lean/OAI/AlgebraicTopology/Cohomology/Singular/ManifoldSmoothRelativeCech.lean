import OAI.AlgebraicTopology.Cohomology.Singular.SmoothRelativeCechTransport
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison

/-! # Manifold Smooth Relative Cech -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothRelativeCech

noncomputable section

/-! The canonical relative-open smooth Čech augmentation is a
quasi-isomorphism, by actual open-subspace transport and the proved
whole-space smooth-small comparison. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable (E X : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace X] [ChartedSpace E X]
variable {ι : Type} (U : ι → Opens X) (W : Opens X) (hsub : ∀ i, U i ≤ W)

/-- The canonical smooth-cochain augmentation for any cover of an open
domain is a quasi-isomorphism. The map is exactly the existing generic
relative-open section augmentation. -/
theorem manifoldSmoothRelativeCechAugmentation_quasiIso
    (hcover : ∀ x : W, ∃ i, (x : X) ∈ U i) :
    QuasiIso (DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation U W hsub
      (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X (ModuleCat.of ℂ ℂ))) :=
  (quasiIso_iff_of_arrow_mk_iso _ _
    (SmoothRelativeCechTransport.manifoldSmoothRelativeCechAugmentationArrowIso E X U W hsub (ModuleCat.of ℂ ℂ))).2
      (ManifoldSmoothCechComparison.manifoldSmoothCechTopAugmentation_quasiIso E W (SmoothRelativeCechTransport.relativeCechOpenCover U W)
        (SmoothRelativeCechTransport.relativeCechOpenCover_covers U W hcover))

/-- A set-membership formulation of the same exact relative-open theorem. -/
theorem manifoldSmoothRelativeCechAugmentation_quasiIso_of_cover
    (hcover : ∀ x ∈ W, ∃ i, x ∈ U i) :
    QuasiIso (DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation U W hsub
      (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X (ModuleCat.of ℂ ℂ))) :=
  manifoldSmoothRelativeCechAugmentation_quasiIso E X U W hsub
    (fun x => hcover x x.property)

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothRelativeCech
