import OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyRealization
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion

/-! # Cycle Stratum Realization -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Analytic realizations of actual cycle supports and smooth strata

The point spaces below are the native complex points of the reduced support
scheme and of its actual algebraic smooth locus. Their manifold structures
come from the proved regular-coordinate construction. The dimension of the
regular locus is identified with the function-field grading of cycles.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped ContDiff _root_.Manifold

section

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}

/-- The actual structure morphism of the piece, as an object over the base. -/
abbrev CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.toOver (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (P.inclusion ≫ f)

/-- The given locally closed inclusion is a morphism over the complex base. -/
def CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.toAmbient (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) : P.toOver ⟶ Over.mk f :=
  Over.homMk P.inclusion rfl

/-- The native analytic point space of the actual smooth piece. -/
abbrev CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSpace (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver

/-- The common dimension derived by the native manifold construction. -/
abbrev CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) : ℕ :=
  Betti.AffineDimension.Realization.functionFieldDifferentialDimension (P.inclusion ≫ f)

abbrev CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticModel (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) := Fin P.complexDimension → ℂ

instance CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSpace_nonempty (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    Nonempty P.analyticSpace :=
  Foundations.Scheme.ComplexPointExistence.nonempty_complexOverPoints (P.inclusion ≫ f)

instance CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSpace_locallyCompact (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    LocallyCompactSpace P.analyticSpace := by
  let : LocallyOfFiniteType P.toOver.hom := inferInstanceAs
    (LocallyOfFiniteType (P.inclusion ≫ f))
  exact ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_locallyCompact P.toOver

instance CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSpace_chartedSpace (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    ChartedSpace P.analyticModel P.analyticSpace := by
  let : IsIntegral P.toOver.left := P.integral
  let : Smooth P.toOver.hom := P.smooth
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace P.toOver

instance CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSpace_complexIsManifold (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) (r : ℕ∞ω) :
    IsManifold (𝓘(ℂ, P.analyticModel)) r P.analyticSpace := by
  let : IsIntegral P.toOver.left := P.integral
  let : Smooth P.toOver.hom := P.smooth
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold P.toOver r

instance CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSpace_realIsManifold (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) (r : ℕ∞ω) :
    IsManifold (𝓘(ℝ, P.analyticModel)) r P.analyticSpace := by
  let : IsIntegral P.toOver.left := P.integral
  let : Smooth P.toOver.hom := P.smooth
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeRealIsManifold P.toOver r

/-- The analytic dimension is the actual transcendence dimension of this piece. -/
theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_eq_dimension (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.complexDimension = P.dimension :=
  (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension
    (P.inclusion ≫ f)).symm

theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticModel_complex_finrank (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    Module.finrank ℂ P.analyticModel = P.dimension := by
  rw [Module.finrank_pi, Fintype.card_fin, P.complexDimension_eq_dimension]

theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticModel_real_finrank (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    Module.finrank ℝ P.analyticModel = 2 * P.dimension := by
  rw [finrank_real_of_complex, P.analyticModel_complex_finrank]

end

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The actual reduced support scheme over its specified complex base. -/
abbrev CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.toOver (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk Z.structureMap

def CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.toAmbient (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : Z.toOver ⟶ V.toOver :=
  Over.homMk Z.inclusion rfl

abbrev CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSpace (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z.toOver

abbrev CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : Z.analyticSpace → V.analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map Z.toAmbient

/-- A possibly singular cycle support is genuinely closed in the analytic variety. -/
theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.isClosedEmbedding_analyticInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Topology.IsClosedEmbedding Z.analyticInclusion := by
  let : IsClosedImmersion Z.toAmbient.left := Z.inclusion_isClosedImmersion
  exact ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion Z.toAmbient

instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSpace_nonempty (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : Nonempty Z.analyticSpace :=
  Foundations.Scheme.ComplexPointExistence.nonempty_complexOverPoints Z.structureMap

instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSpace_compactSpace (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    CompactSpace Z.analyticSpace :=
  Z.projectivePresentation.compactSpace_complexPoints

instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSpace_t2Space (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : T2Space Z.analyticSpace :=
  Z.isClosedEmbedding_analyticInclusion.isEmbedding.t2Space

instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSpace_secondCountableTopology (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    SecondCountableTopology Z.analyticSpace :=
  Z.isClosedEmbedding_analyticInclusion.isEmbedding.secondCountableTopology

/-- The actual open algebraic smooth locus of the reduced support. -/
abbrev CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularScheme (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : Scheme := CycleClass.Geometric.SmoothStratum.smoothStratum Z.structureMap

abbrev CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularToBase (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : Z.regularScheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase :=
  CycleClass.Geometric.SmoothStratum.smoothStratumToBase Z.structureMap

abbrev CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularOver (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk Z.regularToBase

def CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularToSupport (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : Z.regularOver ⟶ Z.toOver :=
  Over.homMk (CycleClass.Geometric.SmoothStratum.smoothStratumι Z.structureMap) rfl

abbrev CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticSpace (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z.regularOver

abbrev CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularAnalyticSpace → Z.analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map Z.regularToSupport

/-- The smooth locus has exactly the topology of an open subset of the support. -/
theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.isOpenEmbedding_regularAnalyticInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Topology.IsOpenEmbedding Z.regularAnalyticInclusion := by
  let : IsOpenImmersion Z.regularToSupport.left := inferInstanceAs
    (IsOpenImmersion (CycleClass.Geometric.SmoothStratum.smoothStratumι Z.structureMap))
  exact ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion Z.regularToSupport

abbrev CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : ℕ :=
  Betti.AffineDimension.Realization.functionFieldDifferentialDimension Z.regularToBase

abbrev CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticModel (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :=
  Fin Z.regularComplexDimension → ℂ

instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticSpace_nonempty (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Nonempty Z.regularAnalyticSpace :=
  Foundations.Scheme.ComplexPointExistence.nonempty_complexOverPoints Z.regularToBase

instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticSpace_t2Space (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    T2Space Z.regularAnalyticSpace :=
  Z.isOpenEmbedding_regularAnalyticInclusion.isEmbedding.t2Space

instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticSpace_secondCountableTopology (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    SecondCountableTopology Z.regularAnalyticSpace :=
  Z.isOpenEmbedding_regularAnalyticInclusion.isEmbedding.secondCountableTopology

instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticSpace_locallyCompact (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    LocallyCompactSpace Z.regularAnalyticSpace := by
  let : LocallyOfFiniteType Z.regularOver.hom := inferInstanceAs
    (LocallyOfFiniteType Z.regularToBase)
  exact ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_locallyCompact Z.regularOver

instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticSpace_chartedSpace (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    ChartedSpace Z.regularAnalyticModel Z.regularAnalyticSpace := by
  let : IsIntegral Z.regularOver.left := inferInstanceAs (IsIntegral Z.regularScheme)
  let : Smooth Z.regularOver.hom := inferInstanceAs (Smooth Z.regularToBase)
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace Z.regularOver

instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticSpace_complexIsManifold (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (r : ℕ∞ω) :
    IsManifold (𝓘(ℂ, Z.regularAnalyticModel)) r Z.regularAnalyticSpace := by
  let : IsIntegral Z.regularOver.left := inferInstanceAs (IsIntegral Z.regularScheme)
  let : Smooth Z.regularOver.hom := inferInstanceAs (Smooth Z.regularToBase)
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold Z.regularOver r

instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticSpace_realIsManifold (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (r : ℕ∞ω) :
    IsManifold (𝓘(ℝ, Z.regularAnalyticModel)) r Z.regularAnalyticSpace := by
  let : IsIntegral Z.regularOver.left := inferInstanceAs (IsIntegral Z.regularScheme)
  let : Smooth Z.regularOver.hom := inferInstanceAs (Smooth Z.regularToBase)
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeRealIsManifold Z.regularOver r

/-- The genuine nonempty smooth open locus has the same function field, so its
manifold dimension is exactly the cycle support dimension. -/
theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_eq_supportDimension (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularComplexDimension = Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 V.structureMap := by
  calc
    Z.regularComplexDimension = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Z.regularToBase :=
      (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension Z.regularToBase).symm
    _ = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Z.structureMap :=
      Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (CycleClass.Geometric.SmoothStratum.smoothStratumι Z.structureMap) Z.structureMap
    _ = Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 V.structureMap := rfl

/-- The cycle codimension equals the difference of the proved manifold dimensions. -/
theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_add_codimension (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularComplexDimension + p = V.complexDimension := by
  rw [Z.regularComplexDimension_eq_supportDimension, Z.dimension_add_codimension]
  exact Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension V.structureMap

theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_eq_sub (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularComplexDimension = V.complexDimension - p := by
  have h := Z.regularComplexDimension_add_codimension
  omega

theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticModel_complex_finrank (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Module.finrank ℂ Z.regularAnalyticModel = V.complexDimension - p := by
  rw [Module.finrank_pi, Fintype.card_fin, Z.regularComplexDimension_eq_sub]

theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticModel_real_finrank (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Module.finrank ℝ Z.regularAnalyticModel = 2 * (V.complexDimension - p) := by
  rw [finrank_real_of_complex, Z.regularAnalyticModel_complex_finrank]

end

end OAI.AlgebraicGeometry
