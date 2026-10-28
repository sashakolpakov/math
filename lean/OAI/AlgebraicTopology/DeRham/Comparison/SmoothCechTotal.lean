import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexAugmentation
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Smooth Cech Total -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechTotal

noncomputable section

/-!
# The signed total complex of actual smooth Čech–de Rham cochains

The degree-k object is mathlib's categorical direct sum of the actual
smooth Čech cochain modules in bidegrees n+p=k. Its differential is the
horizontal Čech differential plus the signed vertical exterior derivative.
-/

open _root_.CategoryTheory

universe u

variable {E ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (U : ι → TopologicalSpace.Opens E)

/-- The total complex uses actual direct sums of the smooth Čech cochain modules. -/
def smoothCechTotal : CochainComplex (ModuleCat.{u} ℂ) ℕ :=
  (SmoothCechDoubleComplex.smoothCechDoubleComplex U).total (ComplexShape.up ℕ)

/-- Inclusion of one actual bidegree into the total cochain module. -/
def smoothCechTotalInclusion (n p k : ℕ) (h : n + p = k) :
    ModuleCat.of ℂ (SmoothCech.SmoothCechCochain U p n) ⟶ (smoothCechTotal U).X k :=
  (SmoothCechDoubleComplex.smoothCechDoubleComplex U).ιTotal (ComplexShape.up ℕ) n p k h

/-- On each actual cochain summand the total differential is `δ + (-1)^n d`. -/
theorem smoothCechTotalInclusion_d (n p k : ℕ) (h : n + p = k) :
    smoothCechTotalInclusion U n p k h ≫ (smoothCechTotal U).d k (k + 1) =
      ModuleCat.ofHom (SmoothCech.smoothCechDelta U p n) ≫
          smoothCechTotalInclusion U (n + 1) p (k + 1) (by omega) +
        ((-1 : ℤ) ^ n) • (ModuleCat.ofHom (SmoothCechDoubleComplex.smoothCechExteriorD U p n) ≫
          smoothCechTotalInclusion U n (p + 1) (k + 1) (by omega)) := by
  have hd := DoubleComplexSigns.DoubleComplex.iota_d_of_eq (SmoothCechDoubleComplex.smoothCechDoubleComplex U) n p k h
  rw [SmoothCechDoubleComplex.smoothCechDoubleComplex_d_f, SmoothCechDoubleComplex.smoothCechDoubleComplex_X_d] at hd
  exact hd

/-- The total differential squares to zero by the proved bicomplex identities. -/
theorem smoothCechTotal_d_squared (k : ℕ) :
    (smoothCechTotal U).d k (k + 1) ≫ (smoothCechTotal U).d (k + 1) (k + 2) = 0 :=
  (smoothCechTotal U).d_comp_d k (k + 1) (k + 2)

/-- The total differential as a complex-linear map of the actual total modules. -/
def smoothCechTotalD (k : ℕ) :
    (smoothCechTotal U).X k →ₗ[ℂ] (smoothCechTotal U).X (k + 1) :=
  ((smoothCechTotal U).d k (k + 1)).hom

theorem smoothCechTotalD_squared (k : ℕ) (c : (smoothCechTotal U).X k) :
    smoothCechTotalD U (k + 1) (smoothCechTotalD U k c) = 0 :=
  congrArg (fun f => f.hom c) (smoothCechTotal_d_squared U k)

variable (W : TopologicalSpace.Opens E) (hsub : ∀ i, U i ≤ W)

/-- The ordinary restriction augmentation induces a genuine map to the total complex. -/
def smoothCechAugmentationToTotal : Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex W ⟶ smoothCechTotal U :=
  DoubleComplexAugmentation.DoubleComplex.augmentationToTotal (SmoothCechDoubleComplex.smoothCechDoubleComplex U)
    (SmoothCechDoubleComplex.smoothCechColumnAugmentation U W hsub) (by
      change SmoothCechDoubleComplex.smoothCechColumnAugmentation U W hsub ≫
        CochainComplex.of.d (SmoothCechDoubleComplex.smoothCechColumn U) (SmoothCechDoubleComplex.smoothCechHorizontal U) 0 (0 + 1) = 0
      rw [CochainComplex.of_d]
      exact SmoothCechDoubleComplex.smoothCechColumnAugmentation_horizontal U W hsub)

@[simp]
theorem smoothCechAugmentationToTotal_f (p : ℕ) :
    (smoothCechAugmentationToTotal U W hsub).f p =
      ModuleCat.ofHom (SmoothCechAugmentation.smoothCechAugmentation U p W hsub) ≫
        smoothCechTotalInclusion U 0 p p (Nat.zero_add p) := rfl

/-- Global forms map to total Čech–de Rham cochains by actual restriction. -/
def smoothCechGlobalAugmentationToTotal : Analysis.DifferentialForms.Manifold.DeRham.deRhamComplex E ⟶ smoothCechTotal U :=
  Analysis.DifferentialForms.Manifold.OpenDeRhamX.deRhamOnOpen ⊤ ≫ smoothCechAugmentationToTotal U ⊤ (fun _ => le_top)

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechTotal
