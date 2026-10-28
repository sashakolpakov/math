import OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldScalar
import OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldFiniteType
import OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport
import OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialTranscendenceDegree
import OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialBaseIso
import OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDegreeTransfer

/-! # Transcendence Dimension -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension

noncomputable section

/-!
# Dimension from the actual function field

For an integral scheme over a field, the structure morphism gives its function
field its canonical scalar algebra. Its transcendence degree therefore defines
a dimension without any choice of an affine presentation. Local finite type
ensures that taking the natural-number value loses no information. On every
nonempty affine open it agrees with the transcendence degree of the actual
ring of sections.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]

/-- The transcendence dimension of an integral scheme over its actual base
field. The finite-type theorem below verifies that the cardinal-to-natural
conversion preserves the full transcendence degree in the intended setting. -/
def schemeTranscendenceDimension (f : X ⟶ Spec (.of K)) : ℕ :=
  letI := FunctionFieldScalar.functionFieldScalarAlgebra f
  (Algebra.trdeg K X.functionField).toNat

/-- The defining expression, with the structure-morphism scalar algebra
made explicit for use in downstream statements. -/
theorem schemeTranscendenceDimension_def (f : X ⟶ Spec (.of K)) :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    schemeTranscendenceDimension f = (Algebra.trdeg K X.functionField).toNat := rfl

/-- For a locally finite-type integral scheme, the natural-number dimension
recovers the complete cardinal-valued transcendence degree. -/
theorem schemeTranscendenceDimension_cast (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    (schemeTranscendenceDimension f : Cardinal) = Algebra.trdeg K X.functionField := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  exact Cardinal.cast_toNat_of_lt_aleph0 (FunctionFieldFiniteType.functionFieldScalar_trdeg_lt_aleph0 f)

/-- Every finite transcendence basis of the actual function field counts
the same dimension. -/
theorem schemeTranscendenceDimension_eq_natCard_basis
    (f : X ⟶ Spec (.of K)) {ι : Type u} [Finite ι] (v : ι → X.functionField) :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    IsTranscendenceBasis K v → schemeTranscendenceDimension f = Nat.card ι := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  intro hv
  exact congrArg Cardinal.toNat hv.cardinalMk_eq_trdeg.symm

/-- The locally finite-type hypothesis supplies an actual finite
transcendence basis of cardinality equal to this dimension. -/
theorem exists_schemeTranscendenceBasis (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    ∃ s : Finset X.functionField, IsTranscendenceBasis K ((↑) : s → X.functionField) ∧
      s.card = schemeTranscendenceDimension f := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldFiniteType.functionFieldScalar_finTrdeg f
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis K X.functionField
  refine ⟨s, hs, ?_⟩
  have h := schemeTranscendenceDimension_eq_natCard_basis f ((↑) : s → X.functionField) hs
  simpa using h.symm

/-- Over a perfect field the same dimension is computed by the genuine
module of Kähler differentials of the function field. -/
theorem schemeTranscendenceDimension_eq_kaehlerFinrank [PerfectField K]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    schemeTranscendenceDimension f = Module.finrank X.functionField Ω[X.functionField⁄K] := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldFiniteType.functionFieldScalar_essFiniteType f
  exact (DifferentialTranscendenceDegree.kaehler_finrank_eq_trdeg K X.functionField).symm

/-- The function-field differential module is finite-dimensional in the
perfect-field locally finite-type setting. -/
theorem functionFieldScalar_kaehlerFinite [PerfectField K]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    Module.Finite X.functionField Ω[X.functionField⁄K] := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldFiniteType.functionFieldScalar_essFiniteType f
  exact DifferentialTranscendenceDegree.kaehler_finite_of_essFiniteType K X.functionField

/-- On any nonempty affine open, the canonical dimension is the
transcendence degree of the actual sections over the actual base field. -/
theorem schemeTranscendenceDimension_eq_affineSections
    (f : X ⟶ Spec (.of K)) (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    letI := SpecScalarTransport.specSectionScalarAlgebra f U
    schemeTranscendenceDimension f = (Algebra.trdeg K Γ(X, U)).toNat := by
  let := SpecScalarTransport.specSectionScalarAlgebra f U
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldScalar.functionFieldScalar_isScalarTower f U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  exact congrArg Cardinal.toNat (TranscendenceDegreeTransfer.trdeg_eq_of_isFractionRing K Γ(X, U) X.functionField).symm

/-- Replacing global functions on the base spectrum by the actual scalar
field leaves the function-field differential dimension unchanged. -/
theorem functionFieldScalar_kaehlerFinrank_eq_base
    (f : X ⟶ Spec (.of K)) :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    Module.finrank X.functionField Ω[X.functionField⁄K] =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension f := by
  let := FunctionFieldScalar.specGlobalScalarAlgebra K
  let := Betti.AffineDimension.Realization.functionFieldBaseAlgebra f
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldScalar.functionFieldBaseScalar_isScalarTower f
  exact (DifferentialBaseIso.kaehlerDifferentialEquivOfSurjectiveBase K Γ(Spec (.of K), ⊤) X.functionField
    (FunctionFieldScalar.specGlobalScalarAlgebra_surjective (K := K))).finrank_eq

/-- In characteristic zero, the canonical transcendence dimension agrees
with the common differential dimension used by the genuine smooth charts. -/
theorem schemeTranscendenceDimension_eq_functionFieldDifferentialDimension
    [CharZero K] (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    schemeTranscendenceDimension f = Betti.AffineDimension.Realization.functionFieldDifferentialDimension f := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  exact (schemeTranscendenceDimension_eq_kaehlerFinrank f).trans
    (functionFieldScalar_kaehlerFinrank_eq_base f)

end

end OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension
