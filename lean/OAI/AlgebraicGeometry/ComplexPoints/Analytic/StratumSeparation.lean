import OAI.AlgebraicGeometry.ComplexPoints.Analytic.CycleStratumRealization
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeImmersionPointTopology
import Mathlib.Topology.Compactness.SigmaCompact

/-! # Stratum Separation -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Separation and countability of actual smooth strata

Scheme immersions give genuine locally closed embeddings of ordinary complex
point spaces. The standard topological transfer theorems therefore apply to
the actual smooth pieces in a projective variety or one of its cycle supports.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace ComplexPoints.Analytic

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- Hausdorffness descends along the point embedding of an actual immersion. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.t2Space_of_isImmersion (φ : X ⟶ Y) [IsImmersion φ.left]
    [T2Space (SchemePointHomeomorphs.schemeComplexPoints Y)] : T2Space (SchemePointHomeomorphs.schemeComplexPoints X) :=
  (SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion φ).t2Space

/-- Second-countability descends along the actual point embedding. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.secondCountableTopology_of_isImmersion (φ : X ⟶ Y) [IsImmersion φ.left]
    [SecondCountableTopology (SchemePointHomeomorphs.schemeComplexPoints Y)] :
    SecondCountableTopology (SchemePointHomeomorphs.schemeComplexPoints X) :=
  (SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion φ).secondCountableTopology

/-- A locally closed immersion into a locally compact point space has a
locally compact source point space. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.locallyCompactSpace_of_isImmersion (φ : X ⟶ Y) [IsImmersion φ.left]
    [LocallyCompactSpace (SchemePointHomeomorphs.schemeComplexPoints Y)] :
    LocallyCompactSpace (SchemePointHomeomorphs.schemeComplexPoints X) :=
  (SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion φ).isInducing.locallyCompactSpace
    (SchemePointHomeomorphs.schemeComplexPoints.isLocallyClosed_range_map_of_isImmersion φ)

/-- Local compactness and second-countability of the ambient point space
give sigma-compactness for an actual immersed point space. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.sigmaCompactSpace_of_isImmersion (φ : X ⟶ Y) [IsImmersion φ.left]
    [LocallyCompactSpace (SchemePointHomeomorphs.schemeComplexPoints Y)]
    [SecondCountableTopology (SchemePointHomeomorphs.schemeComplexPoints Y)] :
    SigmaCompactSpace (SchemePointHomeomorphs.schemeComplexPoints X) := by
  let : LocallyCompactSpace (SchemePointHomeomorphs.schemeComplexPoints X) := SchemePointHomeomorphs.schemeComplexPoints.locallyCompactSpace_of_isImmersion φ
  let : SecondCountableTopology (SchemePointHomeomorphs.schemeComplexPoints X) :=
    SchemePointHomeomorphs.schemeComplexPoints.secondCountableTopology_of_isImmersion φ
  infer_instance

end ComplexPoints.Analytic

section

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}

/-- The actual analytic space of a smooth piece is Hausdorff whenever its
ambient native complex-point space is Hausdorff. -/
theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSpace_t2Space_of_ambient (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f)
    [T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f))] : T2Space P.analyticSpace := by
  let : IsImmersion P.toAmbient.left := P.immersion
  exact ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.t2Space_of_isImmersion P.toAmbient

/-- The actual analytic space of a smooth piece inherits second-countability
from its ambient native complex-point space. -/
theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSpace_secondCountableTopology_of_ambient (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f)
    [SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f))] :
    SecondCountableTopology P.analyticSpace := by
  let : IsImmersion P.toAmbient.left := P.immersion
  exact ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.secondCountableTopology_of_isImmersion P.toAmbient

/-- Algebraic smoothness already supplies local compactness of the piece;
ambient second-countability therefore gives sigma-compactness. -/
theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSpace_sigmaCompactSpace_of_ambient (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f)
    [SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f))] :
    SigmaCompactSpace P.analyticSpace := by
  let : SecondCountableTopology P.analyticSpace := P.analyticSpace_secondCountableTopology_of_ambient
  infer_instance

end

section

/-- Every actual integral smooth piece of a projective variety is Hausdorff. -/
instance Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.stratumAnalyticSpace_t2Space (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece V.structureMap) : T2Space P.analyticSpace := by
  let : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap)) := V.analyticSpace_t2Space
  exact P.analyticSpace_t2Space_of_ambient

/-- Every actual integral smooth piece of a projective variety is second countable. -/
instance Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.stratumAnalyticSpace_secondCountableTopology (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece V.structureMap) :
    SecondCountableTopology P.analyticSpace := by
  let : SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap)) :=
    V.analyticSpace_secondCountableTopology
  exact P.analyticSpace_secondCountableTopology_of_ambient

/-- Local compactness of a projective variety's actual smooth pieces. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.stratumAnalyticSpace_locallyCompactSpace (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece V.structureMap) : LocallyCompactSpace P.analyticSpace :=
  P.analyticSpace_locallyCompact

/-- Every actual integral smooth piece of a projective variety is sigma compact. -/
instance Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.stratumAnalyticSpace_sigmaCompactSpace (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece V.structureMap) : SigmaCompactSpace P.analyticSpace := by
  let : SecondCountableTopology P.analyticSpace := V.stratumAnalyticSpace_secondCountableTopology P
  infer_instance

end

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- Every actual integral smooth piece of a cycle support is Hausdorff. -/
instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.stratumAnalyticSpace_t2Space (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) : T2Space P.analyticSpace := by
  let : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk Z.structureMap)) := Z.analyticSpace_t2Space
  exact P.analyticSpace_t2Space_of_ambient

/-- Every actual integral smooth piece of a cycle support is second countable. -/
instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.stratumAnalyticSpace_secondCountableTopology (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) :
    SecondCountableTopology P.analyticSpace := by
  let : SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk Z.structureMap)) :=
    Z.analyticSpace_secondCountableTopology
  exact P.analyticSpace_secondCountableTopology_of_ambient

/-- Local compactness of a cycle support's actual smooth pieces. -/
theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.stratumAnalyticSpace_locallyCompactSpace (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) : LocallyCompactSpace P.analyticSpace :=
  P.analyticSpace_locallyCompact

/-- Every actual integral smooth piece of a cycle support is sigma compact. -/
instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.stratumAnalyticSpace_sigmaCompactSpace (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) : SigmaCompactSpace P.analyticSpace := by
  let : SecondCountableTopology P.analyticSpace := Z.stratumAnalyticSpace_secondCountableTopology P
  infer_instance

end

end OAI.AlgebraicGeometry
