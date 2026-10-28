import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechTotal
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechPartition
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexComparison
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Smooth Cech Comparison -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechComparison

noncomputable section

/-!
# The actual smooth Čech augmentation comparison

The hypotheses needed for augmented double-complex comparison are proved
from actual smooth gluing and partition-of-unity contraction. No row
exactness or comparison isomorphism is postulated.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

universe u

variable {E ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (U : ι → Opens E)

/-- The genuine column augmentation is injective for an actual open cover. -/
theorem smoothCechColumnAugmentation_injective (W : Opens E) (hsub : ∀ i, U i ≤ W)
    (hcover : (W : Set E) ⊆ ⋃ i, (U i : Set E)) (q : ℕ) :
    Function.Injective ((SmoothCechDoubleComplex.smoothCechColumnAugmentation U W hsub).f q) :=
  SmoothCechAugmentation.smoothCechAugmentation_injective U q W hsub hcover

/-- Smooth gluing gives exactness at the augmentation in the actual bicomplex. -/
theorem smoothCechColumnAugmentation_exact (W : Opens E) (hsub : ∀ i, U i ≤ W)
    (hcover : (W : Set E) ⊆ ⋃ i, (U i : Set E)) (q : ℕ) :
    Function.Exact ((SmoothCechDoubleComplex.smoothCechColumnAugmentation U W hsub).f q)
      (((SmoothCechDoubleComplex.smoothCechDoubleComplex U).d 0 1).f q) := by
  rw [SmoothCechDoubleComplex.smoothCechColumnAugmentation_f, SmoothCechDoubleComplex.smoothCechDoubleComplex_d_f]
  exact LinearMap.exact_iff.mpr (SmoothCechAugmentation.smoothCechAugmentation_range U q W hsub hcover).symm

variable [Fintype ι]

/-- The proved partition homotopy supplies categorical exactness of every positive row term. -/
theorem smoothCechRow_exactAt_of_partition
    (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) E (Set.univ : Set E))
    (hrho : rho.IsSubordinate (fun i => (U i : Set E))) (p q : ℕ) :
    ((SmoothCechDoubleComplex.smoothCechDoubleComplex U).flip.X q).ExactAt (p + 1) := by
  rw [SmoothCechDoubleComplex.smoothCechDoubleComplex_row]
  apply ((SmoothCech.smoothCechComplex U q).exactAt_iff' p (p + 1) (p + 2)
    (by simp) (by simp)).2
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
  change LinearMap.range (((SmoothCech.smoothCechComplex U q).d p (p + 1)).hom) =
    LinearMap.ker (((SmoothCech.smoothCechComplex U q).d (p + 1) (p + 2)).hom)
  rw [SmoothCech.cechComplex_d, SmoothCech.cechComplex_d]
  exact SmoothCechPartition.smoothCechDelta_range_eq_ker U q rho hrho p

/-- Actual finite open covers admit the partition proving positive-row exactness. -/
theorem smoothCechRow_exactAt [FiniteDimensional ℝ E]
    (hcover : ∀ x : E, ∃ i, x ∈ U i) (p q : ℕ) :
    ((SmoothCechDoubleComplex.smoothCechDoubleComplex U).flip.X q).ExactAt (p + 1) := by
  obtain ⟨rho, hrho⟩ := PartitionFormOperators.exists_subordinateSmoothPartition U hcover
  exact smoothCechRow_exactAt_of_partition U rho hrho p q

/-- For an actual finite open cover, restriction to the smooth Čech total
complex preserves all cohomology groups. -/
theorem smoothCechAugmentationToTotal_quasiIso [FiniteDimensional ℝ E]
    (hcover : ∀ x : E, ∃ i, x ∈ U i) :
    QuasiIso (SmoothCechTotal.smoothCechAugmentationToTotal U ⊤ (fun _ => le_top)) := by
  unfold SmoothCechTotal.smoothCechAugmentationToTotal
  apply DoubleComplexComparison.DoubleComplex.augmentationToTotal_quasiIso
  · intro q
    exact smoothCechColumnAugmentation_injective U ⊤ (fun _ => le_top)
      (fun x _ => Set.mem_iUnion.mpr (hcover x)) q
  · intro q
    exact smoothCechColumnAugmentation_exact U ⊤ (fun _ => le_top)
      (fun x _ => Set.mem_iUnion.mpr (hcover x)) q
  · intro p q
    exact smoothCechRow_exactAt U hcover p q

/-- The actual global de Rham complex is quasi-isomorphic to the smooth
Čech–de Rham total complex of every finite open cover. -/
theorem smoothCechGlobalAugmentationToTotal_quasiIso [FiniteDimensional ℝ E]
    (hcover : ∀ x : E, ∃ i, x ∈ U i) :
    QuasiIso (SmoothCechTotal.smoothCechGlobalAugmentationToTotal U) := by
  let : IsIso (Analysis.DifferentialForms.Manifold.OpenDeRhamX.deRhamOnOpen (⊤ : Opens E)) :=
    inferInstanceAs (IsIso (Analysis.DifferentialForms.Manifold.GlobalOpen.deRhamTopIso E).hom)
  let : QuasiIso (SmoothCechTotal.smoothCechAugmentationToTotal U ⊤ (fun _ => le_top)) :=
    smoothCechAugmentationToTotal_quasiIso U hcover
  change QuasiIso (Analysis.DifferentialForms.Manifold.OpenDeRhamX.deRhamOnOpen ⊤ ≫ SmoothCechTotal.smoothCechAugmentationToTotal U ⊤ (fun _ => le_top))
  infer_instance

/-- The canonical cohomology isomorphism is induced by actual restriction
from global forms to the smooth Čech total complex. -/
def smoothCechDeRhamCohomologyIso [FiniteDimensional ℝ E]
    (hcover : ∀ x : E, ∃ i, x ∈ U i) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.DeRham.deRhamCohomology E n ≅ (SmoothCechTotal.smoothCechTotal U).homology n := by
  letI : QuasiIso (SmoothCechTotal.smoothCechGlobalAugmentationToTotal U) :=
    smoothCechGlobalAugmentationToTotal_quasiIso U hcover
  exact isoOfQuasiIsoAt (SmoothCechTotal.smoothCechGlobalAugmentationToTotal U) n

@[simp]
theorem smoothCechDeRhamCohomologyIso_hom [FiniteDimensional ℝ E]
    (hcover : ∀ x : E, ∃ i, x ∈ U i) (n : ℕ) :
    (smoothCechDeRhamCohomologyIso U hcover n).hom =
      HomologicalComplex.homologyMap (SmoothCechTotal.smoothCechGlobalAugmentationToTotal U) n := rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechComparison
