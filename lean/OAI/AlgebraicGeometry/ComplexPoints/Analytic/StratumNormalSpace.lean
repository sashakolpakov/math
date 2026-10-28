import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.CycleStratumRealization
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalEq

/-! # Stratum Normal Space -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.StratumNormalSpace

noncomputable section

/-!
# Actual normal spaces of smooth complex strata

The normal space is the quotient of the target's native tangent space by
the image of the actual manifold differential. Injectivity for algebraic
immersions computes its dimension. Its complex vector-space structure gives
the canonical orientation of its underlying real vector space.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped ContDiff _root_.Manifold

section

/-- The actual tangent space of the proved native complex manifold. -/
abbrev NativeComplexTangent (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :=
  TangentSpace (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) x

instance nativeComplexTangent_finiteDimensional (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral X.left] [Smooth X.hom] (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    FiniteDimensional ℂ (NativeComplexTangent X x) := by
  change FiniteDimensional ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
  infer_instance

theorem nativeComplexTangent_finrank (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral X.left] [Smooth X.hom] (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Module.finrank ℂ (NativeComplexTangent X x) =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom := by
  change Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) = _
  rw [Module.finrank_pi, Fintype.card_fin]

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

/-- The existing complex manifold differential of the genuine point map. -/
abbrev nativeSchemeDifferential (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    NativeComplexTangent X x →L[ℂ] NativeComplexTangent Y (SchemePointHomeomorphs.schemeComplexPoints.map φ x) :=
  mfderiv (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
    (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ))
    (SchemePointHomeomorphs.schemeComplexPoints.map φ) x

/-- The actual image tangent subspace in the target tangent space. -/
def nativeSchemeTangentRange (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Submodule ℂ (NativeComplexTangent Y (SchemePointHomeomorphs.schemeComplexPoints.map φ x)) :=
  LinearMap.range (nativeSchemeDifferential φ x).toLinearMap

@[simp]
theorem mem_nativeSchemeTangentRange (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X)
    (v : NativeComplexTangent Y (SchemePointHomeomorphs.schemeComplexPoints.map φ x)) :
    v ∈ nativeSchemeTangentRange φ x ↔
      ∃ w : NativeComplexTangent X x, nativeSchemeDifferential φ x w = v := Iff.rfl

/-- The normal vector space is the actual quotient by the differential image. -/
abbrev NativeSchemeNormal (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X) :=
  CycleClass.Geometric.ComplexNormalEq.Cycles.ComplexNormal (nativeSchemeTangentRange φ x)

abbrev nativeSchemeNormalProjection (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    NativeComplexTangent Y (SchemePointHomeomorphs.schemeComplexPoints.map φ x) →ₗ[ℂ] NativeSchemeNormal φ x :=
  CycleClass.Geometric.ComplexNormalEq.Cycles.normalProjection (nativeSchemeTangentRange φ x)

/-- A target tangent vector is zero in the normal space exactly when it is
the image of a source tangent vector under the actual differential. -/
@[simp]
theorem nativeSchemeNormalProjection_eq_zero (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X)
    (v : NativeComplexTangent Y (SchemePointHomeomorphs.schemeComplexPoints.map φ x)) :
    nativeSchemeNormalProjection φ x v = 0 ↔
      ∃ w : NativeComplexTangent X x, nativeSchemeDifferential φ x w = v := by
  exact (CycleClass.Geometric.ComplexNormalEq.Cycles.normalProjection_eq_zero (nativeSchemeTangentRange φ x) v).trans
    (mem_nativeSchemeTangentRange φ x v)

theorem nativeSchemeTangentRange_finrank (φ : X ⟶ Y) [IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Module.finrank ℂ (nativeSchemeTangentRange φ x) =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom := by
  exact (LinearMap.finrank_range_of_inj
    (IntrinsicSmoothImmersion.mfderiv_nativeScheme_immersion_injective φ x)).trans (nativeComplexTangent_finrank X x)

/-- Rank-nullity for the actual normal quotient of an algebraic immersion. -/
theorem nativeSchemeNormal_finrank_add (φ : X ⟶ Y) [IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Module.finrank ℂ (NativeSchemeNormal φ x) +
        Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom := by
  have h := (nativeSchemeTangentRange φ x).finrank_quotient_add_finrank
  rw [nativeSchemeTangentRange_finrank φ x,
    nativeComplexTangent_finrank Y (SchemePointHomeomorphs.schemeComplexPoints.map φ x)] at h
  exact h

theorem nativeSchemeNormal_complex_finrank (φ : X ⟶ Y) [IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Module.finrank ℂ (NativeSchemeNormal φ x) =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom -
        Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom := by
  have h := nativeSchemeNormal_finrank_add φ x
  omega

theorem nativeSchemeNormal_real_finrank (φ : X ⟶ Y) [IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Module.finrank ℝ (NativeSchemeNormal φ x) =
      2 * (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom -
        Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) := by
  rw [finrank_real_of_complex, nativeSchemeNormal_complex_finrank φ x]

/-- The existing complex orientation, applied to the actual normal quotient. -/
def nativeSchemeNormalOrientation (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Orientation ℝ (NativeSchemeNormal φ x)
      (Fin (Module.finrank ℂ (NativeSchemeNormal φ x)) × Fin 2) :=
  CycleClass.Geometric.ComplexNormalEq.Cycles.complexNormalOrientation (nativeSchemeTangentRange φ x)

theorem nativeSchemeNormalOrientation_eq_basis (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X)
    (b : Module.Basis (Fin (Module.finrank ℂ (NativeSchemeNormal φ x))) ℂ
      (NativeSchemeNormal φ x)) :
    nativeSchemeNormalOrientation φ x = CycleClass.Geometric.ComplexOrientation.complexOrientationOfBasis b :=
  CycleClass.Geometric.ComplexNormalEq.Cycles.complexNormalOrientation_eq_basis (nativeSchemeTangentRange φ x) b

set_option backward.isDefEq.respectTransparency false in
/-- The actual real differential, with both native tangent-space type synonyms
identified with their common underlying model vector spaces. -/
abbrev nativeSchemeRealDifferential (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    NativeComplexTangent X x →L[ℝ] NativeComplexTangent Y (SchemePointHomeomorphs.schemeComplexPoints.map φ x) :=
  show (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) →L[ℝ]
      (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) from
    mfderiv (𝓘(ℝ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
      (𝓘(ℝ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ))
      (SchemePointHomeomorphs.schemeComplexPoints.map φ) x

set_option backward.isDefEq.respectTransparency false in
theorem nativeSchemeRealDifferential_eq_restrictScalars (φ : X ⟶ Y)
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    nativeSchemeRealDifferential φ x = (nativeSchemeDifferential φ x).restrictScalars ℝ :=
  IntrinsicDerivativeScalars.real_mfderiv_nativeScheme_map_eq_restrictScalars φ x

/-- The range of the actual real manifold differential. -/
def nativeSchemeRealTangentRange (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Submodule ℝ (NativeComplexTangent Y (SchemePointHomeomorphs.schemeComplexPoints.map φ x)) :=
  LinearMap.range (nativeSchemeRealDifferential φ x).toLinearMap

theorem nativeSchemeRealTangentRange_eq_restrictScalars (φ : X ⟶ Y)
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    nativeSchemeRealTangentRange φ x = (nativeSchemeTangentRange φ x).restrictScalars ℝ := by
  unfold nativeSchemeRealTangentRange
  rw [nativeSchemeRealDifferential_eq_restrictScalars]
  rfl

/-- The real normal quotient uses the actual real differential image. -/
abbrev NativeSchemeRealNormal (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X) :=
  NativeComplexTangent Y (SchemePointHomeomorphs.schemeComplexPoints.map φ x) ⧸ nativeSchemeRealTangentRange φ x

/-- The actual real normal quotient is canonically the underlying real vector
space of the actual complex normal quotient. -/
def nativeSchemeRealNormalEquiv (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    NativeSchemeRealNormal φ x ≃ₗ[ℝ] NativeSchemeNormal φ x :=
  (Submodule.quotEquivOfEq (nativeSchemeRealTangentRange φ x)
    ((nativeSchemeTangentRange φ x).restrictScalars ℝ)
    (nativeSchemeRealTangentRange_eq_restrictScalars φ x)).trans
      (CycleClass.Geometric.ComplexNormalEq.Cycles.realNormalEquiv (nativeSchemeTangentRange φ x))

@[simp]
theorem nativeSchemeRealNormalEquiv_projection (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X)
    (v : NativeComplexTangent Y (SchemePointHomeomorphs.schemeComplexPoints.map φ x)) :
    nativeSchemeRealNormalEquiv φ x ((nativeSchemeRealTangentRange φ x).mkQ v) =
      nativeSchemeNormalProjection φ x v := by
  change (CycleClass.Geometric.ComplexNormalEq.Cycles.realNormalEquiv (nativeSchemeTangentRange φ x))
    ((Submodule.quotEquivOfEq (nativeSchemeRealTangentRange φ x)
      ((nativeSchemeTangentRange φ x).restrictScalars ℝ)
      (nativeSchemeRealTangentRange_eq_restrictScalars φ x))
        (Submodule.Quotient.mk v)) = _
  rw [Submodule.quotEquivOfEq_mk]
  rfl

theorem nativeSchemeRealNormal_finrank (φ : X ⟶ Y) [IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Module.finrank ℝ (NativeSchemeRealNormal φ x) =
      2 * (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom -
        Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) := by
  rw [(nativeSchemeRealNormalEquiv φ x).finrank_eq, nativeSchemeNormal_real_finrank φ x]

/-- Transport of the complex orientation gives the orientation of the
actual real differential normal quotient. -/
def nativeSchemeRealNormalOrientation (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Orientation ℝ (NativeSchemeRealNormal φ x)
      (Fin (Module.finrank ℂ (NativeSchemeNormal φ x)) × Fin 2) :=
  (Orientation.map _ (nativeSchemeRealNormalEquiv φ x)).symm
    (nativeSchemeNormalOrientation φ x)

@[simp]
theorem nativeSchemeRealNormalOrientation_map (φ : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Orientation.map _ (nativeSchemeRealNormalEquiv φ x)
      (nativeSchemeRealNormalOrientation φ x) = nativeSchemeNormalOrientation φ x :=
  (Orientation.map _ (nativeSchemeRealNormalEquiv φ x)).apply_symm_apply _

end

namespace DimensionCycleSupport

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

local instance (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : IsIntegral Z.regularOver.left :=
  inferInstanceAs (IsIntegral Z.regularScheme)

local instance (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : Smooth Z.regularOver.hom :=
  inferInstanceAs (Smooth Z.regularToBase)

local instance : IsIntegral V.toOver.left := V.property
local instance : Smooth V.toOver.hom := V.presentation.smooth

/-- The genuine inclusion of the support's smooth locus into the ambient variety. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularToAmbient (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : Z.regularOver ⟶ V.toOver :=
  Z.regularToSupport ≫ Z.toAmbient

instance _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularToAmbient_isImmersion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    IsImmersion Z.regularToAmbient.left := by
  change IsImmersion (CycleClass.Geometric.SmoothStratum.smoothStratumι Z.structureMap ≫ Z.inclusion)
  infer_instance

abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularAnalyticSpace → V.analyticSpace :=
  SchemePointHomeomorphs.schemeComplexPoints.map Z.regularToAmbient

/-- The normal space of the actual smooth-locus inclusion at a native complex point. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.RegularNormalSpace (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (x : Z.regularAnalyticSpace) :=
  NativeSchemeNormal Z.regularToAmbient x

/-- The dimension-defined cycle grading is exactly the complex normal dimension. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularNormalSpace_complex_finrank (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) : Module.finrank ℂ (Z.RegularNormalSpace x) = p := by
  have h := nativeSchemeNormal_finrank_add Z.regularToAmbient x
  change Module.finrank ℂ (Z.RegularNormalSpace x) + Z.regularComplexDimension =
    V.complexDimension at h
  have hdim := Z.regularComplexDimension_add_codimension
  omega

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularNormalSpace_real_finrank (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) : Module.finrank ℝ (Z.RegularNormalSpace x) = 2 * p := by
  rw [finrank_real_of_complex, CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularNormalSpace_complex_finrank]

/-- A complex basis indexed by the actual cycle codimension, used only to
present the canonical orientation; the orientation is basis-independent. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularNormalBasis (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (x : Z.regularAnalyticSpace) :
    Module.Basis (Fin p) ℂ (Z.RegularNormalSpace x) :=
  (Module.finBasis ℂ (Z.RegularNormalSpace x)).reindex
    (finCongr (Z.regularNormalSpace_complex_finrank x))

def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularNormalOrientation (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (x : Z.regularAnalyticSpace) :
    Orientation ℝ (Z.RegularNormalSpace x) (Fin p × Fin 2) :=
  CycleClass.Geometric.ComplexOrientation.complexOrientationOfBasis (Z.regularNormalBasis x)

/-- The real orientation does not depend on the chosen complex normal basis. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularNormalOrientation_eq_basis (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) (b : Module.Basis (Fin p) ℂ (Z.RegularNormalSpace x)) :
    Z.regularNormalOrientation x = CycleClass.Geometric.ComplexOrientation.complexOrientationOfBasis b :=
  CycleClass.Geometric.ComplexOrientation.complexOrientationOfBasis_eq (Z.regularNormalBasis x) b

/-- The quotient by the actual real differential of the smooth-locus inclusion. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.RegularRealNormalSpace (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :=
  NativeSchemeRealNormal Z.regularToAmbient x

def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRealNormalEquiv (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (x : Z.regularAnalyticSpace) :
    Z.RegularRealNormalSpace x ≃ₗ[ℝ] Z.RegularNormalSpace x :=
  nativeSchemeRealNormalEquiv Z.regularToAmbient x

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRealNormalSpace_finrank (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) : Module.finrank ℝ (Z.RegularRealNormalSpace x) = 2 * p := by
  rw [(Z.regularRealNormalEquiv x).finrank_eq, Z.regularNormalSpace_real_finrank x]

def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRealNormalOrientation (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    Orientation ℝ (Z.RegularRealNormalSpace x) (Fin p × Fin 2) :=
  (Orientation.map _ (Z.regularRealNormalEquiv x)).symm (Z.regularNormalOrientation x)

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRealNormalOrientation_map (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    Orientation.map _ (Z.regularRealNormalEquiv x) (Z.regularRealNormalOrientation x) =
      Z.regularNormalOrientation x :=
  (Orientation.map _ (Z.regularRealNormalEquiv x)).apply_symm_apply _

end DimensionCycleSupport

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.StratumNormalSpace
