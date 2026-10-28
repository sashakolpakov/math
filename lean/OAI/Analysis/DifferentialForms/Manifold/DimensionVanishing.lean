import OAI.Analysis.DifferentialForms.Manifold.OpenDeRham
import OAI.Analysis.DifferentialForms.Manifold.OpenDeRhamX
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Dimension Vanishing -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Differential forms above the manifold dimension

An alternating covector of degree exceeding the real dimension vanishes
because every tuple of arguments is linearly dependent. This proves the
actual smooth form spaces, de Rham cochain objects and their cohomology vanish
in those degrees; no cohomological dimension bound is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

/-- Above dimension every continuous alternating covector is zero. -/
theorem DimensionVanishing.formValue_eq_zero_of_finrank_lt (h : Module.finrank ℝ E < n)
    (form : Basic.FormValue E n) : form = 0 := by
  apply ContinuousAlternatingMap.ext
  intro v
  apply form.toAlternatingMap.map_linearDependent v
  intro hv
  have hcard := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  exact (Nat.not_lt_of_ge hcard) h

/-- Actual global smooth forms vanish above the real dimension. -/
theorem Basic.SmoothForm.eq_zero_of_finrank_lt (h : Module.finrank ℝ E < n)
    (form : Basic.SmoothForm E n) : form = 0 := by
  apply Basic.SmoothForm.ext
  intro x
  exact DimensionVanishing.formValue_eq_zero_of_finrank_lt h (form x)

/-- Actual smooth sections on an arbitrary open also vanish above dimension. -/
theorem OpenD.SmoothOpenForm.eq_zero_of_finrank_lt (h : Module.finrank ℝ E < n)
    {U : Opens E} (form : OpenD.SmoothOpenForm U n) : form = 0 := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  exact DimensionVanishing.formValue_eq_zero_of_finrank_lt h (form x)

theorem DimensionVanishing.deRhamComplex_isZero_X_of_finrank_lt (h : Module.finrank ℝ E < n) :
    IsZero ((DeRham.deRhamComplex E).X n) := by
  change IsZero (ModuleCat.of ℂ (Basic.SmoothForm E n))
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  exact ⟨fun form other => (form.eq_zero_of_finrank_lt h).trans
    (other.eq_zero_of_finrank_lt h).symm⟩

theorem DimensionVanishing.openDeRhamComplex_isZero_X_of_finrank_lt (h : Module.finrank ℝ E < n)
    (U : Opens E) : IsZero ((OpenDeRhamX.openDeRhamComplex U).X n) := by
  change IsZero (ModuleCat.of ℂ (OpenD.SmoothOpenForm U n))
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  exact ⟨fun form other => (form.eq_zero_of_finrank_lt h).trans
    (other.eq_zero_of_finrank_lt h).symm⟩

theorem DimensionVanishing.deRhamCohomology_isZero_of_finrank_lt (h : Module.finrank ℝ E < n) :
    IsZero (DeRham.deRhamCohomology E n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (DimensionVanishing.deRhamComplex_isZero_X_of_finrank_lt h)).isZero_homology

theorem DimensionVanishing.openDeRhamCohomology_isZero_of_finrank_lt (h : Module.finrank ℝ E < n)
    (U : Opens E) : IsZero (OpenDeRhamX.openDeRhamCohomology U n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (DimensionVanishing.openDeRhamComplex_isZero_X_of_finrank_lt h U)).isZero_homology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- Every actual raw tangent-covector field above the model dimension vanishes. -/
theorem Algebra.RawManifoldForm.eq_zero_of_finrank_lt (h : Module.finrank ℝ E < n)
    (form : Algebra.RawManifoldForm E M n) : form = 0 := by
  funext x
  exact DimensionVanishing.formValue_eq_zero_of_finrank_lt h (form x)

theorem Algebra.SmoothManifoldForm.eq_zero_of_finrank_lt (h : Module.finrank ℝ E < n)
    (form : Algebra.SmoothManifoldForm E M n) : form = 0 :=
  Subtype.ext (Algebra.RawManifoldForm.eq_zero_of_finrank_lt h (form : Algebra.RawManifoldForm E M n))

theorem Open.SmoothOpenManifoldForm.eq_zero_of_finrank_lt (h : Module.finrank ℝ E < n)
    {U : Opens M} (form : Open.SmoothOpenManifoldForm E U n) : form = 0 := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  exact DimensionVanishing.formValue_eq_zero_of_finrank_lt h (form x)

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem DimensionVanishing.manifoldDeRhamComplex_isZero_X_of_finrank_lt (h : Module.finrank ℝ E < n) :
    IsZero ((ManifoldDeRham.manifoldDeRhamComplex E M).X n) := by
  change IsZero (ModuleCat.of ℂ (Algebra.SmoothManifoldForm E M n))
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  exact ⟨fun form other => (form.eq_zero_of_finrank_lt h).trans
    (other.eq_zero_of_finrank_lt h).symm⟩

theorem DimensionVanishing.openManifoldDeRhamComplex_isZero_X_of_finrank_lt
    (h : Module.finrank ℝ E < n) (U : Opens M) :
    IsZero ((OpenDeRham.openManifoldDeRhamComplex E U).X n) := by
  change IsZero (ModuleCat.of ℂ (Open.SmoothOpenManifoldForm E U n))
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  exact ⟨fun form other => (form.eq_zero_of_finrank_lt h).trans
    (other.eq_zero_of_finrank_lt h).symm⟩

theorem DimensionVanishing.manifoldDeRhamCohomology_isZero_of_finrank_lt (h : Module.finrank ℝ E < n) :
    IsZero (ManifoldDeRham.manifoldDeRhamCohomology E M n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (DimensionVanishing.manifoldDeRhamComplex_isZero_X_of_finrank_lt (M := M) h)).isZero_homology

theorem DimensionVanishing.openManifoldDeRhamCohomology_isZero_of_finrank_lt
    (h : Module.finrank ℝ E < n) (U : Opens M) :
    IsZero (OpenDeRham.openManifoldDeRhamCohomology E U n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (DimensionVanishing.openManifoldDeRhamComplex_isZero_X_of_finrank_lt h U)).isZero_homology

end

end OAI.Analysis.DifferentialForms.Manifold
