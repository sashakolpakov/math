import OAI.Analysis.DifferentialForms.Manifold.SheafDeRham
import OAI.Analysis.DifferentialForms.Manifold.CechAugmentation
import OAI.Analysis.DifferentialForms.Manifold.CechLocallyFinite
import OAI.AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexComparison

/-! # Cech De Rham -/

namespace OAI.Analysis.DifferentialForms.Manifold.CechDeRham

noncomputable section

/-!
The genuine manifold Čech–de Rham double complex and its native total complex.
The augmentation restricts global forms to the given open cover. Its
quasi-isomorphism is proved from actual smooth gluing and the constructed
locally finite partition contraction; no row exactness is assumed.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

universe u

open OAI.AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor

variable (E M : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The complex of genuine manifold-form presheaves and exterior derivatives. -/
def manifoldDeRhamPresheafComplex :
    CochainComplex ((Opens M)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ :=
  CochainComplex.of (ManifoldSheaf.manifoldFormPresheaf E M) (ManifoldSheaf.manifoldFormPresheafD E M)
    (ManifoldSheaf.manifoldFormPresheafD_squared E M)

@[simp]
theorem manifoldDeRhamPresheafComplex_X (p : ℕ) :
    (manifoldDeRhamPresheafComplex E M).X p = ManifoldSheaf.manifoldFormPresheaf E M p := rfl

@[simp]
theorem manifoldDeRhamPresheafComplex_d (p : ℕ) :
    (manifoldDeRhamPresheafComplex E M).d p (p + 1) = ManifoldSheaf.manifoldFormPresheafD E M p :=
  CochainComplex.of_d (ManifoldSheaf.manifoldFormPresheaf E M) (ManifoldSheaf.manifoldFormPresheafD E M) p

/-- The coefficient presheaves are the underlying actual de Rham sheaves. -/
theorem manifoldDeRhamPresheafComplex_X_sheaf (p : ℕ) :
    (manifoldDeRhamPresheafComplex E M).X p =
      ((SheafDeRham.manifoldDeRhamSheafComplex E M).X p).presheaf := rfl

/-- Forgetting the sheaf condition preserves the actual exterior derivative. -/
theorem manifoldDeRhamPresheafComplex_d_sheaf (p : ℕ) :
    (manifoldDeRhamPresheafComplex E M).d p (p + 1) =
      ((SheafDeRham.manifoldDeRhamSheafComplex E M).d p (p + 1)).hom := by
  rw [manifoldDeRhamPresheafComplex_d, SheafDeRham.manifoldDeRhamSheafComplex_d]
  rfl

variable {E M} {ι : Type u} (U : ι → Opens M)

/-- Apply the actual exterior derivative to each Čech section. -/
abbrev manifoldCechExteriorD (p n : ℕ) :
    CechContraction.ManifoldCechCochain (E := E) U p n →ₗ[ℂ]
      CechContraction.ManifoldCechCochain (E := E) U (p + 1) n :=
  AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex.cechCoefficientMap U (ManifoldSheaf.manifoldFormPresheafD E M p) n

@[simp]
theorem manifoldCechExteriorD_apply (p n : ℕ)
    (c : CechContraction.ManifoldCechCochain (E := E) U p n) (a : Fin (n + 1) → ι) :
    manifoldCechExteriorD U p n c a = Open.SmoothOpenManifoldForm.d (c a) := rfl

theorem manifoldCechExteriorD_squared (p n : ℕ)
    (c : CechContraction.ManifoldCechCochain (E := E) U p n) :
    manifoldCechExteriorD U (p + 1) n (manifoldCechExteriorD U p n c) = 0 := by
  funext a
  exact Open.SmoothOpenManifoldForm.d_squared (c a)

/-- Naturality of exterior differentiation gives the actual commuting square. -/
theorem manifoldCechExteriorD_delta (p n : ℕ)
    (c : CechContraction.ManifoldCechCochain (E := E) U p n) :
    manifoldCechExteriorD U p (n + 1) (CechContraction.manifoldCechDelta U p n c) =
      CechContraction.manifoldCechDelta U (p + 1) n (manifoldCechExteriorD U p n c) :=
  AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex.cechCoefficientMap_delta U (ManifoldSheaf.manifoldFormPresheafD E M p) n c

/-- The actual Čech double complex of the manifold de Rham presheaf complex.
The first degree is Čech degree and the second is differential-form degree. -/
def manifoldCechDoubleComplex :
    HomologicalComplex₂ (ModuleCat.{u} ℂ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex U (manifoldDeRhamPresheafComplex E M)

@[simp]
theorem manifoldCechDoubleComplex_XX (n p : ℕ) :
    ((manifoldCechDoubleComplex (E := E) U).X n).X p =
      ModuleCat.of ℂ (CechContraction.ManifoldCechCochain (E := E) U p n) := rfl

@[simp]
theorem manifoldCechDoubleComplex_d_f (n p : ℕ) :
    ((manifoldCechDoubleComplex (E := E) U).d n (n + 1)).f p =
      ModuleCat.ofHom (CechContraction.manifoldCechDelta (E := E) U p n) :=
  AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex_d_f U (manifoldDeRhamPresheafComplex E M) n p

@[simp]
theorem manifoldCechDoubleComplex_X_d (n p : ℕ) :
    ((manifoldCechDoubleComplex (E := E) U).X n).d p (p + 1) =
      ModuleCat.ofHom (manifoldCechExteriorD (E := E) U p n) := by
  change ((AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex U (manifoldDeRhamPresheafComplex E M)).X n).d p (p + 1) = _
  rw [AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex_X_d, manifoldDeRhamPresheafComplex_d]
  rfl

/-- Each horizontal row is the genuine manifold-form Čech complex. -/
theorem manifoldCechDoubleComplex_row (p : ℕ) :
    (manifoldCechDoubleComplex (E := E) U).flip.X p =
      CechContraction.manifoldCechComplex (E := E) U p := rfl

/-- Restriction of global manifold forms augments the zeroth Čech column. -/
def manifoldCechColumnAugmentation :
    ManifoldDeRham.manifoldDeRhamComplex E M ⟶ (manifoldCechDoubleComplex (E := E) U).X 0 :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (CechAugmentation.manifoldCechAugmentation U p))
    (fun p => by
      rw [manifoldCechDoubleComplex_X_d, ManifoldDeRham.manifoldDeRhamComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro form
      funext a
      exact CechAugmentation.manifoldCechAugmentation_d U p form a)

@[simp]
theorem manifoldCechColumnAugmentation_f (p : ℕ) :
    (manifoldCechColumnAugmentation (E := E) U).f p =
      ModuleCat.ofHom (CechAugmentation.manifoldCechAugmentation (E := E) U p) := rfl

/-- The augmentation is annihilated by the first actual horizontal differential. -/
theorem manifoldCechColumnAugmentation_horizontal :
    manifoldCechColumnAugmentation (E := E) U ≫
      (manifoldCechDoubleComplex (E := E) U).d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext p
  rw [HomologicalComplex.comp_f, manifoldCechColumnAugmentation_f,
    manifoldCechDoubleComplex_d_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact CechAugmentation.manifoldCechDelta_augmentation U p form

/-- The native total complex of actual manifold Čech–de Rham cochains. -/
def manifoldCechTotal : CochainComplex (ModuleCat.{u} ℂ) ℕ :=
  (manifoldCechDoubleComplex (E := E) U).total (ComplexShape.up ℕ)

/-- Inclusion of one genuine Čech–de Rham bidegree into its total degree. -/
def manifoldCechTotalInclusion (n p k : ℕ) (h : n + p = k) :
    ModuleCat.of ℂ (CechContraction.ManifoldCechCochain (E := E) U p n) ⟶
      (manifoldCechTotal (E := E) U).X k :=
  (manifoldCechDoubleComplex (E := E) U).ιTotal (ComplexShape.up ℕ) n p k h

/-- The total differential is precisely the Čech differential plus the
exterior derivative with its usual Čech-degree sign. -/
theorem manifoldCechTotalInclusion_d (n p k : ℕ) (h : n + p = k) :
    manifoldCechTotalInclusion (E := E) U n p k h ≫
      (manifoldCechTotal (E := E) U).d k (k + 1) =
      ModuleCat.ofHom (CechContraction.manifoldCechDelta (E := E) U p n) ≫
          manifoldCechTotalInclusion U (n + 1) p (k + 1) (by omega) +
        ((-1 : ℤ) ^ n) • (ModuleCat.ofHom (manifoldCechExteriorD (E := E) U p n) ≫
          manifoldCechTotalInclusion U n (p + 1) (k + 1) (by omega)) := by
  have hd := AlgebraicTopology.DeRham.Comparison.DoubleComplexSigns.DoubleComplex.iota_d_of_eq (manifoldCechDoubleComplex (E := E) U) n p k h
  rw [manifoldCechDoubleComplex_d_f, manifoldCechDoubleComplex_X_d] at hd
  exact hd

theorem manifoldCechTotal_d_squared (k : ℕ) :
    (manifoldCechTotal (E := E) U).d k (k + 1) ≫
      (manifoldCechTotal (E := E) U).d (k + 1) (k + 2) = 0 :=
  (manifoldCechTotal (E := E) U).d_comp_d k (k + 1) (k + 2)

/-- The genuine restriction augmentation from global forms to the total complex. -/
def manifoldCechAugmentationToTotal :
    ManifoldDeRham.manifoldDeRhamComplex E M ⟶ manifoldCechTotal (E := E) U :=
  AlgebraicTopology.DeRham.Comparison.DoubleComplexAugmentation.DoubleComplex.augmentationToTotal (manifoldCechDoubleComplex (E := E) U)
    (manifoldCechColumnAugmentation U) (manifoldCechColumnAugmentation_horizontal U)

@[simp]
theorem manifoldCechAugmentationToTotal_f (p : ℕ) :
    (manifoldCechAugmentationToTotal (E := E) U).f p =
      ModuleCat.ofHom (CechAugmentation.manifoldCechAugmentation (E := E) U p) ≫
        manifoldCechTotalInclusion U 0 p p (Nat.zero_add p) := rfl

variable (hcover : ∀ x : M, ∃ i, x ∈ U i)

include hcover

theorem manifoldCechColumnAugmentation_injective (p : ℕ) :
    Function.Injective ((manifoldCechColumnAugmentation (E := E) U).f p) :=
  CechAugmentation.manifoldCechAugmentation_injective U p hcover

/-- Gluing proves the zero-column exactness required for total comparison. -/
theorem manifoldCechColumnAugmentation_exact (p : ℕ) :
    Function.Exact ((manifoldCechColumnAugmentation (E := E) U).f p)
      (((manifoldCechDoubleComplex (E := E) U).d 0 1).f p) := by
  rw [manifoldCechColumnAugmentation_f, manifoldCechDoubleComplex_d_f]
  exact CechAugmentation.manifoldCechAugmentation_exact U p hcover

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

/-- The constructed locally finite partition contraction proves positive-row
exactness for this actual double complex on an arbitrary open cover. -/
theorem manifoldCechRow_exactAt (n p : ℕ) :
    ((manifoldCechDoubleComplex (E := E) U).flip.X p).ExactAt (n + 1) := by
  rw [manifoldCechDoubleComplex_row]
  exact CechLocallyFinite.manifoldCech_exactAt_succ_of_arbitrary_cover U hcover p n

/-- Global manifold de Rham cohomology is computed by the genuine Čech–de Rham
total complex of any open cover. Every row-exactness hypothesis is discharged. -/
theorem manifoldCechAugmentationToTotal_quasiIso :
    QuasiIso (manifoldCechAugmentationToTotal (E := E) U) := by
  unfold manifoldCechAugmentationToTotal
  apply AlgebraicTopology.DeRham.Comparison.DoubleComplexComparison.DoubleComplex.augmentationToTotal_quasiIso
  · exact manifoldCechColumnAugmentation_injective U hcover
  · exact manifoldCechColumnAugmentation_exact U hcover
  · exact manifoldCechRow_exactAt U hcover

/-- The canonical cohomology isomorphism is induced by actual restriction of
global manifold forms into the Čech–de Rham total complex. -/
def manifoldCechDeRhamCohomologyIso (n : ℕ) :
    ManifoldDeRham.manifoldDeRhamCohomology E M n ≅ (manifoldCechTotal (E := E) U).homology n := by
  letI : QuasiIso (manifoldCechAugmentationToTotal (E := E) U) :=
    manifoldCechAugmentationToTotal_quasiIso U hcover
  exact isoOfQuasiIsoAt (manifoldCechAugmentationToTotal U) n

@[simp]
theorem manifoldCechDeRhamCohomologyIso_hom (n : ℕ) :
    (manifoldCechDeRhamCohomologyIso (E := E) U hcover n).hom =
      HomologicalComplex.homologyMap (manifoldCechAugmentationToTotal (E := E) U) n := rfl

end

end OAI.Analysis.DifferentialForms.Manifold.CechDeRham
