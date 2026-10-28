import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FieldMarkingTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HermitianTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FieldMaps

/-! # Field Marking Ball Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FieldMarkingBallTransport

noncomputable section

/-! An E-linear map carrying two marked ball lines gives the full native
Hodge transport. Its action, integral lattice, and polarization formulas
remain in the given markings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical TensorProduct

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]

theorem standardComplexCoordinates_linear (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (τ : E →ₐ[ℚ] ℂ) :
    RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E ((u.restrictScalars ℚ).toLinearMap.baseChange ℂ x) τ =
      EmbeddedLinearGroup.embeddedLinearIso u τ (RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E x τ) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul z v =>
    rw [LinearMap.baseChange_tmul]
    have hz : RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E (z ⊗ₜ[ℚ] v) τ =
        z • (fun i => τ (v i)) := by
      funext i
      exact RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates_tmul E z v τ i
    rw [hz, map_smul, EmbeddedLinearGroup.embeddedLinearIso_apply]
    funext i
    rw [RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates_tmul]
    change z * τ (u v i) = z * (((LinearMap.toMatrix' u.toLinearMap).map τ).mulVec
      (fun j => τ (v j)) i)
    rw [EmbeddingMatrixTransport.embeddedMatrix_apply]
    rfl

theorem baseChange_fixedFirstComplexInclusion (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    (u.restrictScalars ℚ).toLinearMap.baseChange ℂ (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e₀ v) =
      Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ (LinearEquiv.refl ℂ Geometry.ComplexBall.PrescribedSignsB.Vec) (EmbeddedLinearGroup.embeddedLinearIso u τ (e₀ v)) := by
  apply (RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E).injective
  have hj (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (w : Geometry.ComplexBall.PrescribedSignsB.Vec) : RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e w) = Pi.single τ (e w) :=
    (RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E).apply_symm_apply _
  rw [hj]
  funext σ
  rw [standardComplexCoordinates_linear, hj]
  by_cases hστ : σ = τ
  · subst σ
    rw [Pi.single_eq_same, Pi.single_eq_same]
    rfl
  · rw [Pi.single_eq_of_ne hστ, map_zero, Pi.single_eq_of_ne hστ]

namespace NativeFieldMarking

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FieldMaps.IntrinsicNumberFieldAction

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (mA : let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ;
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))

def precompose (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  exact u.trans mA

theorem precompose_embedding (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (τ : E →ₐ[ℚ] ℂ)
    (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    (FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking A ρ (precompose A ρ mA u)).toLinearMap.baseChange ℂ
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e₀ v) =
    (FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking A ρ mA).toLinearMap.baseChange ℂ
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ (LinearEquiv.refl ℂ Geometry.ComplexBall.PrescribedSignsB.Vec) (EmbeddedLinearGroup.embeddedLinearIso u τ (e₀ v))) := by
  change ((FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking A ρ mA).toLinearMap.comp
    (u.restrictScalars ℚ).toLinearMap).baseChange ℂ _ = _
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply, baseChange_fixedFirstComplexInclusion]

variable (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (mB : let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B) σ;
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)))
    (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)

local notation "PA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A
local notation "PB" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B
local notation "A₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian PA
local notation "B₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian PB

def transport : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀ ≃ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B₀ :=
  FieldMarkingTransport.IntrinsicFieldMarking.periodComparison A ρ mA B σ (precompose B σ mB u)

theorem transport_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : transport A ρ mA B σ mB u (mA v) = mB (u v) :=
  FieldMarkingTransport.IntrinsicFieldMarking.periodComparison_marking A ρ mA B σ (precompose B σ mB u) v

theorem transport_symm_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : (transport A ρ mA B σ mB u).symm (mB v) = mA (u.symm v) := by
  apply (transport A ρ mA B σ mB u).injective
  rw [LinearEquiv.apply_symm_apply, transport_marking, u.apply_symm_apply]

theorem transport_action (a : NumberField.RingOfIntegers E) :
    (transport A ρ mA B σ mB u).toLinearMap.comp
        (IntegralMaps.IntrinsicLinearMaps.rationalLift (IntegralAction.IntrinsicIntegralAction.nativeMap A.abelian PA ρ a)) =
      (IntegralMaps.IntrinsicLinearMaps.rationalLift (IntegralAction.IntrinsicIntegralAction.nativeMap B.abelian PB σ a)).comp
        (transport A ρ mA B σ mB u).toLinearMap := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.abelian PB σ
  apply LinearMap.ext
  intro x
  change transport A ρ mA B σ mB u (NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A.abelian PA ρ a x) =
    NumberFieldAction.IntrinsicNumberFieldAction.rationalAction B.abelian PB σ a (transport A ρ mA B σ mB u x)
  rw [← NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply, ← NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply]
  exact (mA.symm.trans (u.trans mB)).map_smul (a : E) x

theorem transport_polarization
    (hp : ∀ v w, ChernPairing.nativePolarizationForm B (mB (u v)) (mB (u w)) =
      ChernPairing.nativePolarizationForm A (mA v) (mA w)) (x y : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀) :
    ChernPairing.nativePolarizationForm B (transport A ρ mA B σ mB u x) (transport A ρ mA B σ mB u y) =
      ChernPairing.nativePolarizationForm A x y := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  obtain ⟨v, rfl⟩ := mA.surjective x
  obtain ⟨w, rfl⟩ := mA.surjective y
  rw [transport_marking, transport_marking]
  exact hp v w

theorem firstProjection_kernel_eq_of_line_transport
    (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z w : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hz : ∀ v, (FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking A ρ mA).toLinearMap.baseChange ℂ
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e₀ v) ∈ (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A₀).ker ↔
        v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z})
    (hw : ∀ v, (FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking B σ mB).toLinearMap.baseChange ℂ
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e₀ v) ∈ (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B₀).ker ↔
        v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w})
    (hu : (Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}).map
      (NegativeLine.normalizedLineMap e₀ e₀ (EmbeddedLinearGroup.embeddedLinearIso u τ)).toLinearMap =
        Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w}) :
    (FieldMarkingTransport.IntrinsicFieldMarking.firstProjection A ρ mA τ).ker = (FieldMarkingTransport.IntrinsicFieldMarking.firstProjection B σ (precompose B σ mB u) τ).ker := by
  apply Submodule.comap_injective_of_surjective e₀.surjective
  apply Submodule.ext
  intro v
  change (FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking A ρ mA).toLinearMap.baseChange ℂ
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e₀ v) ∈ (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A₀).ker ↔
    (FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking B σ (precompose B σ mB u)).toLinearMap.baseChange ℂ
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e₀ v) ∈ (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B₀).ker
  rw [hz, precompose_embedding]
  let r := NegativeLine.normalizedLineMap e₀ e₀ (EmbeddedLinearGroup.embeddedLinearIso u τ)
  have he : EmbeddedLinearGroup.embeddedLinearIso u τ (e₀ v) = e₀ (r v) := (e₀.apply_symm_apply _).symm
  rw [he]
  change v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} ↔
    (FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking B σ mB).toLinearMap.baseChange ℂ (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e₀ (r v)) ∈ _
  rw [hw, ← hu, Submodule.mem_map_equiv]
  exact (congrArg (fun t => t ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}) (r.symm_apply_apply v)).to_iff.symm

variable [NumberField.IsCMField E]

theorem transport_isHodgeMap_of_line_transport
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hρ : ActionData.RosatiConjugation A ρ) (hσ : ActionData.RosatiConjugation B σ)
    (hp : ∀ v w, ChernPairing.nativePolarizationForm B (mB (u v)) (mB (u w)) =
      ChernPairing.nativePolarizationForm A (mA v) (mA w))
    (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z w : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hz : ∀ v, (FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking A ρ mA).toLinearMap.baseChange ℂ
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E (P.embeddings P.distinguished) e₀ v) ∈ (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A₀).ker ↔
        v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z})
    (hw : ∀ v, (FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking B σ mB).toLinearMap.baseChange ℂ
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E (P.embeddings P.distinguished) e₀ v) ∈ (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B₀).ker ↔
        v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w})
    (hu : (Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}).map
      (NegativeLine.normalizedLineMap e₀ e₀ (EmbeddedLinearGroup.embeddedLinearIso u (P.embeddings P.distinguished))).toLinearMap =
        Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w})
    (hrA : ∀ i, LieRanks.HasLieRank A.abelian ρ
      ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) (P.firstLieRank i))
    (hrB : ∀ i, LieRanks.HasLieRank B.abelian σ
      ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) (P.firstLieRank i)) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A₀) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B₀)
      (transport A ρ mA B σ mB u).toLinearMap := by
  exact FieldMarkingTransport.IntrinsicFieldMarking.periodComparison_isHodgeMap A ρ s hs hg hdegree mA B σ (precompose B σ mB u)
    P hP hρ hσ hp
    (firstProjection_kernel_eq_of_line_transport A ρ mA B σ mB u
      (P.embeddings P.distinguished) e₀ z w hz hw hu) hrA hrB

end NativeFieldMarking

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FieldMarkingBallTransport
