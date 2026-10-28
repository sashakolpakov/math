import OAI.AlgebraicTopology.Cohomology.Singular.CechDoubleComplex
import OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainCechExact
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexComparison

/-! # Cech Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.CechComparison

noncomputable section

/-!
# The canonical singular Čech totalization comparison

The actual augmentation from cover-small singular cochains is a
quasi-isomorphism because its augmented horizontal rows are exact. For an
open cover of the whole space, the proved small-singular comparison then
gives a quasi-isomorphism from ordinary complex singular cochains. All maps
are the previously constructed restriction augmentations.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {ι : Type} (X : TopCat.{0}) (U : ι → Opens X) (M : ModuleCat.{0} ℂ)

/-- Restriction of small cochains into the zeroth Čech column is injective
in each genuine singular degree. -/
theorem smallSingularCechColumnAugmentation_injective (n : ℕ) :
    Function.Injective ((CechDoubleComplex.smallSingularCechColumnAugmentation X U M).f n) :=
  SmallCochainCechExact.smallSingularCechStandardAugmentation_injective X U M n

/-- The kernel of the first actual horizontal differential is precisely
the image of the small-singular augmentation. -/
theorem smallSingularCechColumnAugmentation_exact (n : ℕ) :
    Function.Exact ((CechDoubleComplex.smallSingularCechColumnAugmentation X U M).f n)
      (((CechDoubleComplex.singularCechDoubleComplex X U M).d 0 1).f n) := by
  rw [CechDoubleComplex.smallSingularCechColumnAugmentation_f, CechDoubleComplex.singularCechDoubleComplex_d_f]
  exact SmallCochainCechExact.smallSingularCechStandardAugmentation_exact X U M n

/-- The canonical augmentation from actual small singular cochains to the
native Čech total complex is a quasi-isomorphism for every open family. -/
theorem smallSingularCechAugmentation_quasiIso :
    QuasiIso (CechDoubleComplex.smallSingularCechAugmentation X U M) :=
  DeRham.Comparison.DoubleComplexComparison.DoubleComplex.augmentationToTotal_quasiIso (CechDoubleComplex.singularCechDoubleComplex X U M)
    (CechDoubleComplex.smallSingularCechColumnAugmentation X U M)
    (CechDoubleComplex.smallSingularCechColumnAugmentation_horizontal X U M)
    (smallSingularCechColumnAugmentation_injective X U M)
    (smallSingularCechColumnAugmentation_exact X U M)
    (CechDoubleComplex.singularCechDoubleComplex_row_exact X U M)

/-- The induced isomorphism is the one from the actual small-cochain
restriction augmentation. -/
def smallSingularCechCohomologyIso (n : ℕ) :
    DeRham.Comparison.SmallSingularCochains.smallSingularCohomology M X (fun i => (U i : Set X)) n ≅
      (CechDoubleComplex.singularCechTotal X U M).homology n := by
  letI := smallSingularCechAugmentation_quasiIso X U M
  exact isoOfQuasiIsoAt (CechDoubleComplex.smallSingularCechAugmentation X U M) n

@[simp]
theorem smallSingularCechCohomologyIso_hom (n : ℕ) :
    (smallSingularCechCohomologyIso X U M n).hom =
      HomologicalComplex.homologyMap (CechDoubleComplex.smallSingularCechAugmentation X U M) n := rfl

/-- On an actual open cover, ordinary complex singular cochains map
quasi-isomorphically to the actual Čech total complex by restriction. -/
theorem complexGlobalSingularCechAugmentation_quasiIso
    (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (CechDoubleComplex.globalSingularCechAugmentation X U (ModuleCat.of ℂ ℂ)) := by
  have := SmallCochainComparison.complexSmallSingularRestriction_quasiIso X (fun i => (U i : Set X))
    (fun i => (U i).isOpen) hcover
  have := smallSingularCechAugmentation_quasiIso X U (ModuleCat.of ℂ ℂ)
  rw [CechDoubleComplex.globalSingularCechAugmentation_eq]
  infer_instance

/-- The ordinary complex singular cohomology of a space is canonically
the cohomology of the singular Čech total complex for any actual open cover. -/
def singularCechCohomologyIso (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n ≅
      (CechDoubleComplex.singularCechTotal X U (ModuleCat.of ℂ ℂ)).homology n := by
  letI := complexGlobalSingularCechAugmentation_quasiIso X U hcover
  exact isoOfQuasiIsoAt (CechDoubleComplex.globalSingularCechAugmentation X U (ModuleCat.of ℂ ℂ)) n

/-- The displayed cohomology isomorphism is induced by the genuine global
restriction augmentation, fixing its mathematical meaning. -/
@[simp]
theorem singularCechCohomologyIso_hom (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (singularCechCohomologyIso X U hcover n).hom =
      HomologicalComplex.homologyMap
        (CechDoubleComplex.globalSingularCechAugmentation X U (ModuleCat.of ℂ ℂ)) n := rfl

/-- On cohomology the global augmentation factors through the same actual
small-simplex restriction and its canonical totalization isomorphism. -/
theorem globalSingularCechAugmentation_homologyMap (n : ℕ) :
    HomologicalComplex.homologyMap (CechDoubleComplex.globalSingularCechAugmentation X U M) n =
      DeRham.Comparison.SmallSingularCochains.smallSingularCohomologyRestriction M X (fun i => (U i : Set X)) n ≫
        (smallSingularCechCohomologyIso X U M n).hom := by
  rw [CechDoubleComplex.globalSingularCechAugmentation_eq, HomologicalComplex.homologyMap_comp]
  rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.CechComparison
