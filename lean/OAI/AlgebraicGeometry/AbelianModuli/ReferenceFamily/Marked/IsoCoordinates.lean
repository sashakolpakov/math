import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.IsoPeriodInvariants
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FieldMarkingBallTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups

/-! # Iso Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.IsoCoordinates

noncomputable section

/-! Recover the actual rational coordinate change of a PEL isomorphism
in arbitrary full field markings. Common ordered exponential labels
give congruence on the same integral lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical _root_.CategoryTheory.MonObj

local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral C.toOver.left := C.variety.property
local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth C.toOver.hom := C.variety.presentation.smooth

theorem native_division_difference_integral (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (N : ℕ)
    (v w : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods C)
    (h : HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints C.toOver) ((N : ℝ)⁻¹ • v.val) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints C.toOver) ((N : ℝ)⁻¹ • w.val)) :
    (N : ℚ)⁻¹ • (v - w) ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods C := by
  change HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expAddHom (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints C.toOver)
    ((N : ℚ)⁻¹ • (v.val - w.val)) = 0
  have hs : (N : ℚ)⁻¹ • (v.val - w.val) =
      (N : ℝ)⁻¹ • v.val - (N : ℝ)⁻¹ • w.val := by
    rw [← Rat.cast_smul_eq_qsmul ℝ, Rat.cast_inv, Rat.cast_natCast, smul_sub]
  rw [hs, map_sub, sub_eq_zero]
  exact congrArg Additive.ofMul h

namespace NativeFieldMarking

variable {E : Type} [Field E] [NumberField E]

theorem baseChange_normalized_inclusion (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (τ : E →ₐ[ℚ] ℂ) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    (u.restrictScalars ℚ).toLinearMap.baseChange ℂ (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e v) =
      Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e (NegativeLine.normalizedLineMap e e (EmbeddedLinearGroup.embeddedLinearIso u τ) v) := by
  rw [Intrinsic.FieldMarkingBallTransport.baseChange_fixedFirstComplexInclusion]
  apply (RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E).injective
  have hj (e' : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (w : Geometry.ComplexBall.PrescribedSignsB.Vec) : RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e' w) = Pi.single τ (e' w) :=
    (RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E).apply_symm_apply _
  rw [hj, hj]
  have hn : e (NegativeLine.normalizedLineMap e e (EmbeddedLinearGroup.embeddedLinearIso u τ) v) =
      EmbeddedLinearGroup.embeddedLinearIso u τ (e v) := e.apply_symm_apply _
  rw [hn]
  rfl

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (α : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B)
    (hα : ∀ a, ρ.map a ≫ α.abelian.hom = α.abelian.hom ≫ σ.map a)
    (mA : let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))
    (mB : let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B) σ
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)))

def isoCoordinates : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E :=
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B) σ
  mA.trans ((Polarized.IsoPeriodInvariants.levelIsoFieldEquiv A B α ρ σ hα).trans mB.symm)

theorem isoCoordinates_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    mB (isoCoordinates A B ρ σ α hα mA mB v) = Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv A B α (mA v) := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B) σ
  exact mB.apply_symm_apply _

theorem isoCoordinates_integral (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))
    (hA : ∀ v, mA v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)) ↔ v ∈ Λ)
    (hB : ∀ v, mB v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)) ↔ v ∈ Λ)
    (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : v ∈ Λ ↔ isoCoordinates A B ρ σ α hα mA mB v ∈ Λ := by
  rw [← hB (isoCoordinates A B ρ σ α hα mA mB v), isoCoordinates_marking,
    Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv_integral, hA]

theorem isoCoordinates_polarization (ψ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E → NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E → ℚ)
    (hA : ∀ v w, Intrinsic.ChernPairing.nativePolarizationForm A (mA v) (mA w) = ψ v w)
    (hB : ∀ v w, Intrinsic.ChernPairing.nativePolarizationForm B (mB v) (mB w) = ψ v w)
    (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    ψ (isoCoordinates A B ρ σ α hα mA mB v) (isoCoordinates A B ρ σ α hα mA mB w) = ψ v w := by
  rw [← hB, isoCoordinates_marking, isoCoordinates_marking, Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv_polarization, hA]

theorem isoCoordinates_complex (v : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    (Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking B σ mB).toLinearMap.baseChange ℂ
      (((isoCoordinates A B ρ σ α hα mA mB).restrictScalars ℚ).toLinearMap.baseChange ℂ v) =
    (Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv A B α).toLinearMap.baseChange ℂ
      ((Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking A ρ mA).toLinearMap.baseChange ℂ v) := by
  have hm : (Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking B σ mB).toLinearMap.comp
      ((isoCoordinates A B ρ σ α hα mA mB).restrictScalars ℚ).toLinearMap =
      (Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv A B α).toLinearMap.comp (Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking A ρ mA).toLinearMap := by
    apply LinearMap.ext
    intro x
    exact isoCoordinates_marking A B ρ σ α hα mA mB x
  have hh := congrArg (fun f : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ]
      Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)) =>
      f.baseChange ℂ v) hm
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using hh

theorem isoCoordinates_congruence [NeZero N]
    (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))
    (hB : ∀ v, mB v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)) ↔ v ∈ Λ)
    (label : Λ → Multiplicative (Fin (2 * g) → ZMod N))
    (hAlevel : ∀ l, Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint A (label l) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)).toOver)
        ((N : ℝ)⁻¹ • (mA l.val).val))
    (hBlevel : ∀ l, Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint B (label l) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)).toOver)
        ((N : ℝ)⁻¹ • (mB l.val).val))
    (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hv : v ∈ Λ) :
    ∃ y ∈ Λ, isoCoordinates A B ρ σ α hα mA mB v - v = N • y := by
  let u := isoCoordinates A B ρ σ α hα mA mB
  have ha := Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv_level A B α (label ⟨v, hv⟩) (N : ℝ)⁻¹ (mA v) (hAlevel ⟨v, hv⟩)
  have hb := hBlevel ⟨v, hv⟩
  have hex : HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)).toOver)
      ((N : ℝ)⁻¹ • (mB (u v)).val) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)).toOver)
        ((N : ℝ)⁻¹ • (mB v).val) := by
    rw [isoCoordinates_marking]
    exact ha.symm.trans hb
  have hint := native_division_difference_integral
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)) N (mB (u v)) (mB v) hex
  have hmap : mB ((N : ℚ)⁻¹ • (u v - v)) = (N : ℚ)⁻¹ • (mB (u v) - mB v) := by
    change Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking B σ mB ((N : ℚ)⁻¹ • (u v - v)) =
      (N : ℚ)⁻¹ • (Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking B σ mB (u v) - Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking B σ mB v)
    rw [map_smul, map_sub]
  refine ⟨(N : ℚ)⁻¹ • (u v - v), (hB _).mp (hmap.symm ▸ hint), ?_⟩
  exact (TorsionCongruence.TorusTorsion.nat_smul_inverse N (u v - v)).symm

theorem isoCoordinates_first_kernel
    (τ : E →ₐ[ℚ] ℂ) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z w : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hz : ∀ v, (Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking A ρ mA).toLinearMap.baseChange ℂ
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e v) ∈
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))).ker ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z})
    (hw : ∀ v, (Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking B σ mB).toLinearMap.baseChange ℂ
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e v) ∈
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B))).ker ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w}) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    NegativeLine.normalizedLineMap e e (EmbeddedLinearGroup.embeddedLinearIso (isoCoordinates A B ρ σ α hα mA mB) τ) v ∈
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w} ↔ v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} := by
  let u := isoCoordinates A B ρ σ α hα mA mB
  let r := NegativeLine.normalizedLineMap e e (EmbeddedLinearGroup.embeddedLinearIso u τ)
  have hj : (u.restrictScalars ℚ).toLinearMap.baseChange ℂ (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e v) =
      Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e (r v) := baseChange_normalized_inclusion u τ e v
  rw [← hw, ← hj, isoCoordinates_complex, Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv_kernel, hz]

theorem isoCoordinates_line_action
    (τ : E →ₐ[ℚ] ℂ) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z w : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hz : ∀ v, (Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking A ρ mA).toLinearMap.baseChange ℂ
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e v) ∈
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))).ker ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z})
    (hw : ∀ v, (Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking B σ mB).toLinearMap.baseChange ℂ
      (Real.PeriodEmbeddingChanges.fixedFirstComplexInclusion E τ e v) ∈
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B))).ker ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w}) :
    w = NegativeLine.negativeLineCoordinate
      (NegativeLine.normalizedLineMap e e (EmbeddedLinearGroup.embeddedLinearIso (isoCoordinates A B ρ σ α hα mA mB) τ) (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) := by
  let r := NegativeLine.normalizedLineMap e e (EmbeddedLinearGroup.embeddedLinearIso (isoCoordinates A B ρ σ α hα mA mB) τ)
  have hm : r (Geometry.ComplexBall.PrescribedSignsB.lineVector z) ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w} :=
    (isoCoordinates_first_kernel A B ρ σ α hα mA mB τ e z w hz hw (Geometry.ComplexBall.PrescribedSignsB.lineVector z)).mpr
      (Submodule.subset_span (Set.mem_singleton _))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have hr : r (Geometry.ComplexBall.PrescribedSignsB.lineVector z) ≠ 0 := by
    intro h
    have hv : Geometry.ComplexBall.PrescribedSignsB.lineVector z = 0 := r.injective (h.trans (map_zero r).symm)
    have hz : (1 : ℂ) = 0 := congrFun hv 2
    exact one_ne_zero hz
  have hcn : c ≠ 0 := by
    intro h
    subst c
    rw [zero_smul] at hc
    exact hr hc.symm
  rw [← hc, NegativeLine.negativeLineCoordinate_smul c hcn, NegativeLine.negativeLineCoordinate_lineVector]

end NativeFieldMarking

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.IsoCoordinates
