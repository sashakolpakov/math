import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplexPeriodAction
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.TensorCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking

/-! # Complex Tate Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplexTateCoordinates.Construction

noncomputable section

/-!
Construct the rational split coordinates of the actual complex Tate
module from the rank-three E-period space. The original integral action
has precisely the prescribed local character in each coordinate block.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking

variable {E L : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

def complexPeriodEBasis :
    letI := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
    Module.Basis (Fin 3) E (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) := by
  letI := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  exact (Pi.basisFun E (Fin 3)).map (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs rfl hdegree).symm

def complexTateEmbeddingCoordinates :
    TateComparison.Rational.rationalTateModule A.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q ≃ₗ[ℚ_[q]] (Fin 3 → Gal(E/ℚ) → ℚ_[q]) := by
  letI := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  letI := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A P ρ
  exact (ComplexPeriodAction.Construction.complexPeriodTateComparison A P q).symm.trans
    (IsogenyQuotient.Field.TensorCoordinates.Construction.fieldTensorCoordinates j iota hsplit (complexPeriodEBasis s hs hdegree A P ρ))

theorem complexTateEmbeddingCoordinates_action (a : NumberField.RingOfIntegers E)
    (x : TateComparison.Rational.rationalTateModule A.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) (i : Fin 3) (τ : Gal(E/ℚ)) :
    complexTateEmbeddingCoordinates j iota hsplit s hs hdegree A P ρ
        (TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) (ρ.map a) x) i τ =
      RationalSplitCompletion.Construction.l45FieldCharacter j iota τ (a : E) *
        complexTateEmbeddingCoordinates j iota hsplit s hs hdegree A P ρ x i τ := by
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A P ρ
  let B := complexPeriodEBasis s hs hdegree A P ρ
  let C := ComplexPeriodAction.Construction.complexPeriodTateComparison A P q
  have h := LinearMap.congr_fun (ComplexPeriodAction.Construction.complexPeriodTateComparison_action A P q ρ a) (C.symm x)
  change TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) (ρ.map a) (C (C.symm x)) =
    C ((AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A P ρ a).baseChange ℚ_[q] (C.symm x)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  have he : AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A P ρ a = Algebra.lsmul ℚ ℚ (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) (a : E) := by
    apply LinearMap.ext
    intro v
    exact (AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply A P ρ a v).symm
  change IsogenyQuotient.Field.TensorCoordinates.Construction.fieldTensorCoordinates j iota hsplit B
      (C.symm (TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) (ρ.map a) x)) i τ =
    RationalSplitCompletion.Construction.l45FieldCharacter j iota τ (a : E) * IsogenyQuotient.Field.TensorCoordinates.Construction.fieldTensorCoordinates j iota hsplit B (C.symm x) i τ
  rw [h, LinearEquiv.symm_apply_apply, he]
  exact IsogenyQuotient.Field.TensorCoordinates.Construction.fieldTensorCoordinates_scalar_action j iota hsplit B (a : E) (C.symm x) i τ

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplexTateCoordinates.Construction
