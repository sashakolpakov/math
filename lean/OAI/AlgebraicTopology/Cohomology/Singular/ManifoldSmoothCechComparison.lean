import OAI.AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmallComparison
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexComparison

/-! # Manifold Smooth Cech Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison

noncomputable section

/-!
# The actual smooth singular Čech totalization comparison

The checked augmented horizontal rows identify small smooth cochains with
the native Čech total complex. For an actual open cover, the proved smooth
small-simplex comparison gives the same result for global complex smooth
cochains. The generic presheaf-section augmentation is identified explicitly
with this map through the canonical top-open cochain isomorphism.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (X : Type) [TopologicalSpace X] [ChartedSpace E X]
variable {ι : Type} (U : ι → Opens X) (A : ModuleCat.{0} ℂ)

/-- The genuine small-smooth augmentation is degreewise injective. -/
theorem smallManifoldSmoothCechColumnAugmentation_injective (n : ℕ) :
    Function.Injective ((SmoothCechDoubleComplex.smallManifoldSmoothCechColumnAugmentation E X U A).f n) :=
  ManifoldSmoothSmallCech.manifoldSmoothSmallCechStandardAugmentation_injective E X U A n

/-- The zeroth horizontal kernel is precisely the actual small-smooth
augmentation image. -/
theorem smallManifoldSmoothCechColumnAugmentation_exact (n : ℕ) :
    Function.Exact ((SmoothCechDoubleComplex.smallManifoldSmoothCechColumnAugmentation E X U A).f n)
      (((SmoothCechDoubleComplex.manifoldSmoothCechDoubleComplex E X U A).d 0 1).f n) := by
  rw [SmoothCechDoubleComplex.smallManifoldSmoothCechColumnAugmentation_f, SmoothCechDoubleComplex.manifoldSmoothCechDoubleComplex_d_f]
  exact ManifoldSmoothSmallCech.manifoldSmoothSmallCechStandardAugmentation_exact E X U A n

/-- The canonical small-smooth augmentation to the native total complex
is a quasi-isomorphism for every open family. -/
theorem smallManifoldSmoothCechAugmentation_quasiIso :
    QuasiIso (SmoothCechDoubleComplex.smallManifoldSmoothCechAugmentation E X U A) :=
  DeRham.Comparison.DoubleComplexComparison.DoubleComplex.augmentationToTotal_quasiIso (SmoothCechDoubleComplex.manifoldSmoothCechDoubleComplex E X U A)
    (SmoothCechDoubleComplex.smallManifoldSmoothCechColumnAugmentation E X U A)
    (SmoothCechDoubleComplex.smallManifoldSmoothCechColumnAugmentation_horizontal E X U A)
    (smallManifoldSmoothCechColumnAugmentation_injective E X U A)
    (smallManifoldSmoothCechColumnAugmentation_exact E X U A)
    (SmoothCechDoubleComplex.manifoldSmoothCechDoubleComplex_row_exact E X U A)

/-- The corresponding isomorphism is induced by the actual small-smooth
augmentation, with no choice of a comparison map. -/
def smallManifoldSmoothCechCohomologyIso (n : ℕ) :
    ManifoldSmoothSmall.manifoldSmoothSmallCohomology E A X (fun i => (U i : Set X)) n ≅
      (SmoothCechDoubleComplex.manifoldSmoothCechTotal E X U A).homology n := by
  letI := smallManifoldSmoothCechAugmentation_quasiIso E X U A
  exact isoOfQuasiIsoAt (SmoothCechDoubleComplex.smallManifoldSmoothCechAugmentation E X U A) n

@[simp]
theorem smallManifoldSmoothCechCohomologyIso_hom (n : ℕ) :
    (smallManifoldSmoothCechCohomologyIso E X U A n).hom =
      HomologicalComplex.homologyMap (SmoothCechDoubleComplex.smallManifoldSmoothCechAugmentation E X U A) n := rfl

/-- Global complex smooth cochains map quasi-isomorphically to the
actual Čech total complex for any open cover. -/
theorem complexGlobalManifoldSmoothCechAugmentation_quasiIso
    (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation E X U (ModuleCat.of ℂ ℂ)) := by
  have := ManifoldSmoothSmallComparison.complexManifoldSmoothSmallRestriction_quasiIso E X (fun i => (U i : Set X))
    (fun i => (U i).isOpen) hcover
  have := smallManifoldSmoothCechAugmentation_quasiIso E X U (ModuleCat.of ℂ ℂ)
  rw [SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation_eq]
  infer_instance

/-- The generic section augmentation at the top open subset is the same
quasi-isomorphism under the canonical actual cochain identification. -/
theorem manifoldSmoothCechTopAugmentation_quasiIso
    (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation U ⊤ (fun _ => le_top)
      (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X (ModuleCat.of ℂ ℂ))) := by
  have h := complexGlobalManifoldSmoothCechAugmentation_quasiIso E X U hcover
  rw [SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation_eq_top] at h
  exact quasiIso_of_comp_left (ManifoldSmoothSections.manifoldSmoothPresheafTopIso E X (ModuleCat.of ℂ ℂ)).inv
    (DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation U ⊤ (fun _ => le_top)
      (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X (ModuleCat.of ℂ ℂ)))

/-- Actual global smooth cohomology is canonically the cohomology of the
native smooth Čech total complex for every open cover. -/
def manifoldSmoothCechCohomologyIso
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) X).homology n ≅
      (SmoothCechDoubleComplex.manifoldSmoothCechTotal E X U (ModuleCat.of ℂ ℂ)).homology n := by
  letI := complexGlobalManifoldSmoothCechAugmentation_quasiIso E X U hcover
  exact isoOfQuasiIsoAt (SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation E X U (ModuleCat.of ℂ ℂ)) n

/-- The forward cohomology map is the one induced by the actual global
restriction augmentation. -/
@[simp]
theorem manifoldSmoothCechCohomologyIso_hom
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (manifoldSmoothCechCohomologyIso E X U hcover n).hom =
      HomologicalComplex.homologyMap
        (SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation E X U (ModuleCat.of ℂ ℂ)) n := rfl

/-- The global cohomology comparison factors through the actual small
restriction and the checked small-smooth Čech isomorphism. -/
theorem globalManifoldSmoothCechAugmentation_homologyMap (n : ℕ) :
    HomologicalComplex.homologyMap (SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation E X U A) n =
      HomologicalComplex.homologyMap
        (ManifoldSmoothSmall.manifoldSmoothSmallRestriction E A X (fun i => (U i : Set X))) n ≫
          (smallManifoldSmoothCechCohomologyIso E X U A n).hom := by
  rw [SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation_eq, HomologicalComplex.homologyMap_comp]
  rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison
