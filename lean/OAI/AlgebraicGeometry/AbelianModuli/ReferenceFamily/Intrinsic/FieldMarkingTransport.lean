import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.RealPeriodChanges
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMTypeHodgeCriterion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactHodgeParts
import OAI.RepresentationTheory.Theta.Geometric.MarkedPolarizationIsometry
import OAI.RepresentationTheory.Theta.Geometric.EmbeddedNormalizedTransport
import OAI.RepresentationTheory.Theta.Geometric.StandardComplexCoordinates

/-! # Field Marking Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking

noncomputable section

/-! Full field markings on the original complex PEL objects determine
their native Hodge comparison from the active kernel and polarization.
The comparison retains the original objects and their period markings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactHodgeParts.IntrinsicHermitianMarking

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

local notation "PA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A
local notation "A₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian PA

variable (mA : let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ;
  NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))

def coordinates : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  exact mA.trans (PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree)

def rationalMarking : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀ := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian PA ρ
  exact mA.restrictScalars ℚ

theorem marking_complexCoordinates (x : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (τ : E →ₐ[ℚ] ℂ) :
    EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree
        ((rationalMarking A ρ mA).toLinearMap.baseChange ℂ x) τ =
      EmbeddedLinearGroup.embeddedLinearIso (coordinates A ρ s hs hg hdegree mA) τ
        (RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E x τ) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian PA ρ
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul z v =>
    rw [LinearMap.baseChange_tmul]
    change RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E
      (PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree)
        (z ⊗ₜ[ℚ] mA v) τ = _
    have hz : RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E (z ⊗ₜ[ℚ] v) τ =
        z • (fun i => τ (v i)) := by
      funext i
      exact RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates_tmul E z v τ i
    rw [hz, map_smul, EmbeddedLinearGroup.embeddedLinearIso_apply]
    funext i
    rw [RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates_tmul]
    change z * τ (PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree (mA v) i) =
      z * (((LinearMap.toMatrix' (coordinates A ρ s hs hg hdegree mA).toLinearMap).map τ).mulVec
        (fun j => τ (v j)) i)
    rw [EmbeddingMatrixTransport.embeddedMatrix_apply]
    rfl

theorem marking_embedding (τ : E →ₐ[ℚ] ℂ) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    (rationalMarking A ρ mA).toLinearMap.baseChange ℂ
        (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ (LinearEquiv.refl ℂ Geometry.ComplexBall.PrescribedSignsB.Vec) v) =
      Real.PeriodEmbeddingChanges.complexEmbeddingInclusion A₀ E
        (PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A ρ s hs hg hdegree) τ
          (EmbeddedLinearGroup.embeddedLinearIso (coordinates A ρ s hs hg hdegree mA) τ v) := by
  apply (EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree).injective
  change EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree
      ((rationalMarking A ρ mA).toLinearMap.baseChange ℂ
        (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ (LinearEquiv.refl ℂ Geometry.ComplexBall.PrescribedSignsB.Vec) v)) =
    Real.PeriodHodgeTransport.complexMarkedPeriodCoordinates A₀ E
      (PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A ρ s hs hg hdegree)
      (Real.PeriodEmbeddingChanges.complexEmbeddingInclusion A₀ E
        (PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A ρ s hs hg hdegree) τ
          (EmbeddedLinearGroup.embeddedLinearIso (coordinates A ρ s hs hg hdegree mA) τ v))
  rw [Real.PeriodEmbeddingChanges.complexEmbeddingInclusion_coordinates]
  funext σ
  rw [marking_complexCoordinates]
  have hj : RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ (LinearEquiv.refl ℂ Geometry.ComplexBall.PrescribedSignsB.Vec) v) = Pi.single τ v :=
    (RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E).apply_symm_apply _
  rw [hj]
  by_cases hστ : σ = τ
  · subst σ
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hστ, Pi.single_eq_of_ne hστ, map_zero]

def firstProjection (τ : E →ₐ[ℚ] ℂ) : Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A₀ :=
  (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A₀).comp
    ((rationalMarking A ρ mA).toLinearMap.baseChange ℂ |>.comp
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ (LinearEquiv.refl ℂ Geometry.ComplexBall.PrescribedSignsB.Vec)))

theorem firstProjection_kernel (τ : E →ₐ[ℚ] ℂ) :
    (firstProjection A ρ mA τ).ker =
      (EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ).comap
        (EmbeddedLinearGroup.embeddedLinearIso (coordinates A ρ s hs hg hdegree mA) τ).toLinearMap := by
  apply Submodule.ext
  intro v
  change PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A₀
    ((rationalMarking A ρ mA).toLinearMap.baseChange ℂ
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ (LinearEquiv.refl ℂ Geometry.ComplexBall.PrescribedSignsB.Vec) v)) = 0 ↔ _
  rw [marking_embedding A ρ s hs hg hdegree,
    PEL.RealPeriodChanges.IntrinsicPELRealChanges.embeddingInclusion_kernel A ρ s hs hg hdegree]
  rfl

theorem coordinates_polarization (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm A ρ s hs hg hdegree
      (coordinates A ρ s hs hg hdegree mA v) (coordinates A ρ s hs hg hdegree mA w) =
        ChernPairing.nativePolarizationForm A (mA v) (mA w) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian PA ρ
  let c := PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree
  change ChernPairing.nativePolarizationForm A (c.symm (c (mA v))) (c.symm (c (mA w))) = _
  rw [c.symm_apply_apply, c.symm_apply_apply]

variable (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)

local notation "PB" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B
local notation "B₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian PB

variable (mB : let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B) σ;
  NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)))

def coordinateChange : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E :=
  (coordinates A ρ s hs hg hdegree mA).symm.trans (coordinates B σ s hs hg hdegree mB)

def periodComparison : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀ ≃ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B₀ :=
  (rationalMarking A ρ mA).symm.trans (rationalMarking B σ mB)

theorem periodComparison_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    periodComparison A ρ mA B σ mB (mA v) = mB v := by
  exact congrArg (rationalMarking B σ mB) ((rationalMarking A ρ mA).symm_apply_apply v)

theorem periodComparison_eq_marked :
    periodComparison A ρ mA B σ mB =
      Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.abelian B.abelian PA PB ρ σ s hs hg hdegree
        (coordinateChange A ρ s hs hg hdegree mA B σ mB) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.abelian PB σ
  apply LinearEquiv.ext
  intro x
  obtain ⟨v, rfl⟩ := mA.surjective x
  rw [periodComparison_marking]
  apply (PELMarking.IntrinsicPELMarking.coordinates B.abelian PB σ s hs hg hdegree).injective
  rw [Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport_coordinates]
  exact (congrArg (coordinates B σ s hs hg hdegree mB)
    ((coordinates A ρ s hs hg hdegree mA).symm_apply_apply v)).symm

theorem coordinateChange_polarization
    (hp : ∀ v w, ChernPairing.nativePolarizationForm B (mB v) (mB w) = ChernPairing.nativePolarizationForm A (mA v) (mA w))
    (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm B σ s hs hg hdegree
      (coordinateChange A ρ s hs hg hdegree mA B σ mB v)
      (coordinateChange A ρ s hs hg hdegree mA B σ mB w) =
        HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm A ρ s hs hg hdegree v w := by
  obtain ⟨v₀, rfl⟩ := (coordinates A ρ s hs hg hdegree mA).surjective v
  obtain ⟨w₀, rfl⟩ := (coordinates A ρ s hs hg hdegree mA).surjective w
  simp only [coordinateChange, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [coordinates_polarization, coordinates_polarization]
  exact hp v₀ w₀

variable [NumberField.IsCMField E]

include hs hg hdegree in
theorem periodComparison_isHodgeMap (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hρ : ActionData.RosatiConjugation A ρ) (hσ : ActionData.RosatiConjugation B σ)
    (hp : ∀ v w, ChernPairing.nativePolarizationForm B (mB v) (mB w) = ChernPairing.nativePolarizationForm A (mA v) (mA w))
    (hk : (firstProjection A ρ mA (P.embeddings P.distinguished)).ker =
      (firstProjection B σ mB (P.embeddings P.distinguished)).ker)
    (hrA : ∀ i, LieRanks.HasLieRank A.abelian ρ
      ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) (P.firstLieRank i))
    (hrB : ∀ i, LieRanks.HasLieRank B.abelian σ
      ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) (P.firstLieRank i)) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A₀) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B₀)
      (periodComparison A ρ mA B σ mB).toLinearMap := by
  rw [periodComparison_eq_marked A ρ s hs hg hdegree mA B σ mB]
  apply CMTypeHodgeCriterion.NativeHermitianMarking.markedPeriodTransport_isHodgeMap_of_CMType A B ρ σ s hs hg hdegree hρ hσ
    P.imaginaryScalar hP.2.2.2.2.2.2.1
    (coordinateChange A ρ s hs hg hdegree mA B σ mB) P.embeddings hP.1.2
  · exact RepresentationTheory.Theta.Geometric.MarkedPolarizationIsometry.markedPolarization_isometry_hermitian A B ρ σ s hs hg hdegree hρ hσ
      P.imaginaryScalar hP.2.2.2.2.2.2.1 (coordinateChange A ρ s hs hg hdegree mA B σ mB)
      (coordinateChange_polarization A ρ s hs hg hdegree mA B σ mB hp)
  · intro i
    by_cases hi : i = P.distinguished
    · subst i
      apply RepresentationTheory.Theta.Geometric.EmbeddedNormalizedTransport.embeddedNormalizedSubmodule_transport
      exact ((firstProjection_kernel A ρ s hs hg hdegree mA _).symm.trans hk).trans
        (firstProjection_kernel B σ s hs hg hdegree mB _)
    · apply CompactHodgeParts.IntrinsicHermitianMarking.nativePositivePart_map_of_extreme_ranks A ρ s hs hg hdegree (P.embeddings i)
        B σ (coordinateChange A ρ s hs hg hdegree mA B σ mB)
        (r := P.firstLieRank i) ?_ (hrA i) (hrB i)
      unfold Datum.RankThreePELDatum.firstLieRank
      rw [ite_eq_right hi]
      split <;> simp

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking
