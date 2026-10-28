import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionNormalForm
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionComplementDimension
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement

/-! # Intrinsic Immersion Normal Pair -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicImmersionNormalPair

noncomputable section

/-!
# Native scheme and regular-locus normal pairs

These are applications of the proved manifold normal-pair construction to
actual complex scheme points and to the regular locus of an algebraic cycle
inside the complement of its singular boundary. Both the immersion normal
form and the full-image embedding property are supplied by proved results.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped ContDiff _root_.Manifold _root_.Topology

section

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

/-- The complex complement supplied by the proved native immersion normal
form, rather than an additional normal-space parameter. -/
abbrev NativeSchemeChartComplement (φ : X ⟶ Y) [IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :=
  (ImmersionNormalForm.nativeScheme_isImmersionAt φ x).complement

instance nativeSchemeChartComplement_finiteDimensional (φ : X ⟶ Y) [IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    FiniteDimensional ℂ (NativeSchemeChartComplement φ x) :=
  ImmersionComplementDimension.immersionComplement_finiteDimensional (ImmersionNormalForm.nativeScheme_isImmersionAt φ x)

/-- The complex normal-chart dimension is forced by the actual source and
target dimensions. -/
theorem nativeSchemeChartComplement_complex_finrank (φ : X ⟶ Y) [IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Module.finrank ℂ (NativeSchemeChartComplement φ x) =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom -
        Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom := by
  change Module.finrank ℂ (ImmersionNormalForm.nativeScheme_isImmersionAt φ x).complement = _
  rw [ImmersionComplementDimension.immersionComplement_finrank,
    Module.finrank_fin_fun, Module.finrank_fin_fun]

theorem nativeSchemeChartComplement_real_finrank (φ : X ⟶ Y) [IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Module.finrank ℝ (NativeSchemeChartComplement φ x) =
      2 * (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom -
        Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) := by
  rw [finrank_real_of_complex, nativeSchemeChartComplement_complex_finrank]

/-- An actual full-image normal pair for an immersion of smooth integral
complex schemes, on their native analytic point spaces. -/
def nativeSchemeNormalPair (φ : X ⟶ Y) [IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    NormalPairRecenter.ImmersionNormalPair ModelX (NativeSchemeChartComplement φ x)
      (SchemePointHomeomorphs.schemeComplexPoints.map φ) x :=
  NormalPairRecenter.immersionNormalPair (ImmersionNormalForm.nativeScheme_isImmersionAt φ x)
    (SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion φ)

/-- The zero normal slice is exactly the native points above the actual
scheme-theoretic image of the immersion. -/
theorem nativeSchemeNormalPair_mem_support (φ : X ⟶ Y) [IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) (y : (nativeSchemeNormalPair φ x).neighborhood) :
    SchemePointHomeomorphs.schemeComplexPoints.underlying y.val ∈ Set.range φ.left ↔
      ((nativeSchemeNormalPair φ x).homeomorph y).2.val = 0 := by
  change y.val ∈ SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range φ.left ↔ _
  rw [← SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion φ]
  exact (nativeSchemeNormalPair φ x).mem_range_iff y

/-- The full underlying scheme image in the chosen analytic neighborhood
is precisely the zero normal coordinate plane. -/
theorem nativeSchemeNormalPair_image_support (φ : X ⟶ Y) [IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    (nativeSchemeNormalPair φ x).ambientChart ''
        ((nativeSchemeNormalPair φ x).neighborhood ∩
          (SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range φ.left)) =
      Metric.ball (0 : ModelX) (nativeSchemeNormalPair φ x).radius ×ˢ
        ({0} : Set (NativeSchemeChartComplement φ x)) := by
  rw [← SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion φ]
  exact (nativeSchemeNormalPair φ x).ambientChart_image_support

/-- Native normal pairs are cofinal in all ambient neighborhoods of the
image point; the actual coordinate map is preserved during shrinking. -/
theorem nativeSchemeNormalPair_cofinal (φ : X ⟶ Y) [IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) (U : Set (SchemePointHomeomorphs.schemeComplexPoints Y))
    (hU : U ∈ 𝓝 (SchemePointHomeomorphs.schemeComplexPoints.map φ x)) :
    ∃ P : NormalPairRecenter.ImmersionNormalPair ModelX (NativeSchemeChartComplement φ x)
        (SchemePointHomeomorphs.schemeComplexPoints.map φ) x,
      P.ambientChart = (nativeSchemeNormalPair φ x).ambientChart ∧ P.neighborhood ⊆ U :=
  (nativeSchemeNormalPair φ x).exists_subpair U hU

end

namespace DimensionCycleSupport

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The actual regular-locus embedding in the complement of its singular
boundary has a proved complex analytic immersion normal form. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplement_isImmersionAt (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    Manifold.IsImmersionAt 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, V.analyticModel) ω
      Z.regularComplementInclusion x :=
  ImmersionNormalForm.isImmersionAt_of_injective_mfderiv Z.regularComplementInclusion x
    (Z.contMDiff_regularComplementInclusion ω x)
    (Z.mfderiv_regularComplementInclusion_injective x)

/-- The actual complex chart complement for the regular-locus embedding. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.RegularComplementChartComplement (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :=
  (Z.regularComplement_isImmersionAt x).complement

instance _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementChartComplement_finiteDimensional (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) : FiniteDimensional ℂ (Z.RegularComplementChartComplement x) :=
  ImmersionComplementDimension.immersionComplement_finiteDimensional (Z.regularComplement_isImmersionAt x)

/-- The actual normal chart of a codimension-`p` cycle has complex normal
dimension exactly `p`. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementChartComplement_complex_finrank (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    Module.finrank ℂ (Z.RegularComplementChartComplement x) = p := by
  change Module.finrank ℂ (Z.regularComplement_isImmersionAt x).complement = p
  rw [ImmersionComplementDimension.immersionComplement_finrank,
    V.analyticModel_complex_finrank, Z.regularAnalyticModel_complex_finrank]
  have hd := Z.regularComplexDimension_add_codimension
  omega

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementChartComplement_real_finrank (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    Module.finrank ℝ (Z.RegularComplementChartComplement x) = 2 * p := by
  rw [finrank_real_of_complex, CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementChartComplement_complex_finrank]

/-- A genuine complex continuous linear identification with the normal
coordinate space of the cycle's actual codimension. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementChartEquivFin (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    Z.RegularComplementChartComplement x ≃L[ℂ] (Fin p → ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [Z.regularComplementChartComplement_complex_finrank x, Module.finrank_fin_fun])

/-- The proved full-image normal pair in the actual boundary-complement
ambient manifold. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementNormalPair (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Z.RegularComplementChartComplement x)
      Z.regularComplementInclusion x :=
  NormalPairRecenter.immersionNormalPair (Z.regularComplement_isImmersionAt x)
    Z.isClosedEmbedding_regularComplementInclusion.isEmbedding

/-- Inside the boundary complement, the zero normal slice is exactly the
original algebraic cycle's analytic support. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementNormalPair_mem_support (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) (y : (Z.regularComplementNormalPair x).neighborhood) :
    (y.val : V.analyticSpace) ∈ Set.range Z.analyticInclusion ↔
      ((Z.regularComplementNormalPair x).homeomorph y).2.val = 0 := by
  change y.val ∈ Subtype.val ⁻¹' Set.range Z.analyticInclusion ↔ _
  rw [← Z.range_regularComplementInclusion]
  exact (Z.regularComplementNormalPair x).mem_range_iff y

/-- Literal equality with the zero normal coordinate plane for the original
cycle support, after deletion of its singular boundary. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementNormalPair_image_support (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    (Z.regularComplementNormalPair x).ambientChart ''
        ((Z.regularComplementNormalPair x).neighborhood ∩
          (Subtype.val ⁻¹' Set.range Z.analyticInclusion)) =
      Metric.ball (0 : Z.regularAnalyticModel) (Z.regularComplementNormalPair x).radius ×ˢ
        ({0} : Set (Z.RegularComplementChartComplement x)) := by
  rw [← Z.range_regularComplementInclusion]
  exact (Z.regularComplementNormalPair x).ambientChart_image_support

/-- These genuine cycle-support normal pairs are cofinal in arbitrary
neighborhoods in the boundary-complement ambient manifold. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementNormalPair_cofinal (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) (U : Set Z.regularAmbientSpace)
    (hU : U ∈ 𝓝 (Z.regularComplementInclusion x)) :
    ∃ P : NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel
        (Z.RegularComplementChartComplement x) Z.regularComplementInclusion x,
      P.ambientChart = (Z.regularComplementNormalPair x).ambientChart ∧ P.neighborhood ⊆ U :=
  (Z.regularComplementNormalPair x).exists_subpair U hU

/-- Cofinality also holds for neighborhoods in the original ambient
variety, after taking the actual open-subspace inclusion. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementNormalPair_cofinal_ambient (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) (U : Set V.analyticSpace)
    (hU : U ∈ 𝓝 (Z.regularAnalyticToAmbient x)) :
    ∃ P : NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel
        (Z.RegularComplementChartComplement x) Z.regularComplementInclusion x,
      P.ambientChart = (Z.regularComplementNormalPair x).ambientChart ∧
        Subtype.val '' P.neighborhood ⊆ U := by
  have hpre : Subtype.val ⁻¹' U ∈ 𝓝 (Z.regularComplementInclusion x) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hU
  obtain ⟨P, he, hP⟩ := Z.regularComplementNormalPair_cofinal x (Subtype.val ⁻¹' U) hpre
  exact ⟨P, he, by rintro y ⟨z, hz, rfl⟩; exact hP hz⟩

end DimensionCycleSupport

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicImmersionNormalPair
