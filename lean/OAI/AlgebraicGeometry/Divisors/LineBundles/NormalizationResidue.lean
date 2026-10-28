import OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueBoundaryAddition
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields

/-! # Normalization Residue -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationResidue.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual residue boundaries on the finite normalization

The existing finite normalization is Noetherian, has integrally closed
stalks, and preserves the original function field and its base scalars.
These facts instantiate the geometric residue construction on a concrete
normal scheme even when the original integral support is singular.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include f in
theorem finiteNormalization_noetherian : AlgebraicGeometry.IsNoetherian (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) := by
  let : IsFinite (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap_isFinite X f
  let : IsLocallyNoetherian (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) :=
    LocallyOfFiniteType.isLocallyNoetherian (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f)
  let : CompactSpace (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) :=
    QuasiCompact.compactSpace_of_compactSpace (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X)
  exact ⟨⟩

def normalizationScalarFieldEquiv :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f)
    X.functionField ≃ₐ[ℂ] (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X).functionField := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f)
  exact AlgEquiv.ofBijective
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldAlgHom (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationMap_genericPoint X) f)
    (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldMap_bijective X)

omit [AlgebraicGeometry.IsNoetherian X] [LocallyOfFiniteType f] in
theorem finiteNormalization_dimension :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f)
  exact congrArg Cardinal.toNat (normalizationScalarFieldEquiv X f).trdeg_eq.symm

def normalizationFunctionUnit (g : X.functionFieldˣ) : (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X).functionFieldˣ :=
  Units.map (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom.hom.toMonoidHom g

/-- The complete actual residue boundary on the finite normalization of the support. -/
def normalizedResidueBoundaryCycle (g h : X.functionFieldˣ) : (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) →₀ ℚ :=
  letI := finiteNormalization_noetherian X f
  Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization_stalk_integrallyClosed X)
    (normalizationFunctionUnit X g) (normalizationFunctionUnit X h)

def normalizedGradedResidueBoundaryCycle (d : ℕ) (g h : X.functionFieldˣ) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f) d →₀ ℚ :=
  letI := finiteNormalization_noetherian X f
  Normal.PointResidue.BundleCycles.normalGradedResidueBoundaryCycle (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization_stalk_integrallyClosed X)
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f) d (normalizationFunctionUnit X g) (normalizationFunctionUnit X h)

theorem normalizedGradedResidueBoundaryCycle_push (d : ℕ) (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 2)
    (g h : X.functionFieldˣ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f) d (normalizedGradedResidueBoundaryCycle X f d g h) =
      normalizedResidueBoundaryCycle X f g h := by
  let := finiteNormalization_noetherian X f
  let : IsFinite (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap_isFinite X f
  exact Normal.PointResidue.BundleCycles.normalGradedResidueBoundaryCycle_push (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization_stalk_integrallyClosed X)
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f) d ((finiteNormalization_dimension X f).trans hX) _ _

theorem normalizedGradedResidueBoundaryCycle_chow_zero (d : ℕ) (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 2)
    (g h : X.functionFieldˣ) :
    letI := finiteNormalization_noetherian X f
    DimensionChow.BundleCycles.dimensionCycleToChowQ (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f) d (normalizedGradedResidueBoundaryCycle X f d g h) = 0 := by
  let := finiteNormalization_noetherian X f
  let : IsFinite (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap_isFinite X f
  exact Normal.PointResidue.BundleCycles.normalGradedResidueBoundaryCycle_chow_zero (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization_stalk_integrallyClosed X)
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f) d ((finiteNormalization_dimension X f).trans hX) _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationResidue.BundleCycles
