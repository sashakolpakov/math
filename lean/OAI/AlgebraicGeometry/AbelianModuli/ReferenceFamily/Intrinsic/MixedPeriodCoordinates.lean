import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RealPeriodMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MixedFromComplexComponents
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Mixed Period Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MixedPeriodCoordinates

noncomputable section

/-! The original rational period marking extends to an actual real
equivalence with the mixed embedding space. Arbitrary complex maps at the
selected places therefore act on the native real tangent space, with an
exact comparison on every rational period. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open _root_.NumberField _root_.NumberField.mixedEmbedding
open scoped TensorProduct _root_.NumberField

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RealPeriodMaps.IntrinsicRationalPeriods

variable (E : Type) [Field E] [NumberField E] [aE : Algebra ℚ E]

def mixedScalarRealification : ℝ ⊗[ℚ] E ≃ₗ[ℝ] mixedSpace E := by
  cases Subsingleton.elim aE (DivisionRing.toRatAlgebra : Algebra ℚ E)
  exact ((NumberField.integralBasis E).baseChange ℝ).equiv
    (NumberField.mixedEmbedding.latticeBasis E) (Equiv.refl _)

theorem mixedScalarRealification_one_tmul (a : E) :
    mixedScalarRealification E (1 ⊗ₜ[ℚ] a) = mixedEmbedding E a := by
  cases Subsingleton.elim aE (DivisionRing.toRatAlgebra : Algebra ℚ E)
  have h : ((mixedScalarRealification E).toLinearMap.restrictScalars ℚ).comp
      (TensorProduct.mk ℚ ℝ E 1) = (mixedEmbedding E).toRatAlgHom.toLinearMap := by
    apply (NumberField.integralBasis E).ext
    intro i
    change mixedScalarRealification E (1 ⊗ₜ[ℚ] NumberField.integralBasis E i) =
      mixedEmbedding E (NumberField.integralBasis E i)
    rw [← Module.Basis.baseChange_apply]
    simp only [mixedScalarRealification, Module.Basis.equiv_apply, Equiv.refl_apply,
      NumberField.mixedEmbedding.latticeBasis_apply]
  exact LinearMap.congr_fun h a

def mixedVectorRealification :
    ℝ ⊗[ℚ] (Fin 3 → E) ≃ₗ[ℝ] (Fin 3 → mixedSpace E) :=
  (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 3 => E)).trans
    (LinearEquiv.piCongrRight (fun _ : Fin 3 => mixedScalarRealification E))

theorem mixedVectorRealification_one_tmul (x : Fin 3 → E) :
    mixedVectorRealification E (1 ⊗ₜ[ℚ] x) =
      fun i => mixedEmbedding E (x i) := by
  funext i
  exact mixedScalarRealification_one_tmul E (x i)

def mixedTraceFunctional (ξ : E) : mixedSpace E →ₗ[ℝ] ℝ :=
  (NumberField.mixedEmbedding.latticeBasis E).constr ℝ
    (fun i => (Algebra.trace ℚ E (ξ * NumberField.integralBasis E i) : ℝ))

theorem mixedTraceFunctional_embedding (ξ a : E) :
    mixedTraceFunctional E ξ (mixedEmbedding E a) = (Algebra.trace ℚ E (ξ * a) : ℝ) := by
  cases Subsingleton.elim aE (DivisionRing.toRatAlgebra : Algebra ℚ E)
  have h : ((mixedTraceFunctional E ξ).restrictScalars ℚ).comp
      (mixedEmbedding E).toRatAlgHom.toLinearMap =
      (Algebra.linearMap ℚ ℝ).comp
        ((Algebra.trace ℚ E).comp (LinearMap.mul ℚ E ξ)) := by
    apply (NumberField.integralBasis E).ext
    intro i
    change mixedTraceFunctional E ξ (mixedEmbedding E (NumberField.integralBasis E i)) =
      (Algebra.trace ℚ E (ξ * NumberField.integralBasis E i) : ℝ)
    rw [← NumberField.mixedEmbedding.latticeBasis_apply, mixedTraceFunctional,
      Module.Basis.constr_basis]
  exact LinearMap.congr_fun h a

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

def nativePeriodRealification :
    ℝ ⊗[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A :=
  ((RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A).baseChange ℝ).equiv (RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A) (Equiv.refl _)

theorem nativePeriodRealification_one_tmul (x : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    nativePeriodRealification A (1 ⊗ₜ[ℚ] x) = x.val := by
  have h : ((nativePeriodRealification A).toLinearMap.restrictScalars ℚ).comp
      (TensorProduct.mk ℚ ℝ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) 1) = (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A).subtype := by
    apply (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A).ext
    intro i
    change nativePeriodRealification A (1 ⊗ₜ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i) =
      (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i).val
    rw [← Module.Basis.baseChange_apply]
    simpa only [nativePeriodRealification, Module.Basis.equiv_apply, Equiv.refl_apply]
      using (RealPeriodMaps.IntrinsicRationalPeriods.rationalPeriodBasis_real A i).symm
  exact LinearMap.congr_fun h x

def nativeMixedPeriodCoordinates (e : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] (Fin 3 → E)) :
    HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℝ] (Fin 3 → mixedSpace E) :=
  (nativePeriodRealification A).symm.trans
    ((e.baseChange ℚ ℝ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) (Fin 3 → E)).trans
      (mixedVectorRealification E))

theorem nativeMixedPeriodCoordinates_rational
    (e : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] (Fin 3 → E)) (x : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    nativeMixedPeriodCoordinates E A e x.val = fun i => mixedEmbedding E (e x i) := by
  have hx : (nativePeriodRealification A).symm x.val = 1 ⊗ₜ[ℚ] x :=
    (nativePeriodRealification A).symm_apply_eq.mpr (nativePeriodRealification_one_tmul A x).symm
  change mixedVectorRealification E
    (e.baseChange ℚ ℝ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) (Fin 3 → E)
      ((nativePeriodRealification A).symm x.val)) = _
  rw [hx]
  exact mixedVectorRealification_one_tmul E (e x)

theorem nativeMixedPeriodCoordinates_intertwines
    (e : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] (Fin 3 → E))
    (f : Module.End ℝ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) (g : Module.End ℚ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A))
    (hg : ∀ x : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A, f x.val = (g x).val)
    (a : E) (he : ∀ x, e (g x) = a • e x) (x : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    nativeMixedPeriodCoordinates E A e (f x) =
      mixedEmbedding E a • nativeMixedPeriodCoordinates E A e x := by
  let m : Module.End ℝ (Fin 3 → mixedSpace E) := {
    toFun v := mixedEmbedding E a • v
    map_add' v w := smul_add _ v w
    map_smul' r v := smul_comm _ r v }
  have h : (nativeMixedPeriodCoordinates E A e).toLinearMap.comp f =
      m.comp (nativeMixedPeriodCoordinates E A e).toLinearMap := by
    apply (RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).ext
    intro i
    change nativeMixedPeriodCoordinates E A e (f (RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i)) =
      mixedEmbedding E a • nativeMixedPeriodCoordinates E A e (RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i)
    rw [← RealPeriodMaps.IntrinsicRationalPeriods.rationalPeriodBasis_real, hg, nativeMixedPeriodCoordinates_rational,
      nativeMixedPeriodCoordinates_rational, he]
    funext j
    exact (mixedEmbedding E).map_mul a (e (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i) j)
  exact LinearMap.congr_fun h x

variable [IsCMField E] {Place : Type*} [Fintype Place]
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective
      (fun p : Place × Bool => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (e : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] (Fin 3 → E))

def nativeMixedComponentChange (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) :
    HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A :=
  (nativeMixedPeriodCoordinates E A e).trans
    (((MixedFromComplexComponents.cmMixedOfComplexComponents σ hσ q).restrictScalars ℝ).trans
      (nativeMixedPeriodCoordinates E A e).symm)

omit [Fintype Place] in
theorem nativeMixedComponentChange_coordinates
    (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (x : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    nativeMixedPeriodCoordinates E A e (nativeMixedComponentChange E A σ hσ e q x) =
      MixedFromComplexComponents.cmMixedOfComplexComponents σ hσ q (nativeMixedPeriodCoordinates E A e x) := by
  simp only [nativeMixedComponentChange, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.apply_symm_apply]

omit [Fintype Place] in
theorem nativeMixedComponentChange_selected
    (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (x : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (p : Place) :
    CMSelectedMixed.cmSelectedMixedCoordinates σ hσ
        (nativeMixedPeriodCoordinates E A e (nativeMixedComponentChange E A σ hσ e q x)) p =
      q p (CMSelectedMixed.cmSelectedMixedCoordinates σ hσ (nativeMixedPeriodCoordinates E A e x) p) := by
  rw [nativeMixedComponentChange_coordinates, MixedFromComplexComponents.cmMixedOfComplexComponents_intertwines]

omit [Fintype Place] in
theorem nativeMixedComponentChange_commutes
    (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (f : Module.End ℝ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) (g : Module.End ℚ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A))
    (hg : ∀ x : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A, f x.val = (g x).val)
    (a : E) (he : ∀ x, e (g x) = a • e x) (x : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    nativeMixedComponentChange E A σ hσ e q (f x) =
      f (nativeMixedComponentChange E A σ hσ e q x) := by
  apply (nativeMixedPeriodCoordinates E A e).injective
  rw [nativeMixedComponentChange_coordinates,
    nativeMixedPeriodCoordinates_intertwines E A e f g hg a he,
    nativeMixedPeriodCoordinates_intertwines E A e f g hg a he,
    nativeMixedComponentChange_coordinates]
  exact (MixedFromComplexComponents.cmMixedOfComplexComponents σ hσ q).map_smul (mixedEmbedding E a) _

def nativeMixedHermitianForm (H : Matrix (Fin 3) (Fin 3) E) :
    HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] mixedSpace E :=
  (CMMixedHermitianForm.cmMixedHermitianForm H).compl₁₂
    (nativeMixedPeriodCoordinates E A e).toLinearMap
    (nativeMixedPeriodCoordinates E A e).toLinearMap

theorem nativeMixedHermitianForm_rational
    (H : Matrix (Fin 3) (Fin 3) E) (x y : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    nativeMixedHermitianForm E A e H x.val y.val =
      mixedEmbedding E (Datum.RankThreePELDatum.matrixHermitian H (e x) (e y)) := by
  change CMMixedHermitianForm.cmMixedHermitianForm H (nativeMixedPeriodCoordinates E A e x.val)
    (nativeMixedPeriodCoordinates E A e y.val) = _
  rw [nativeMixedPeriodCoordinates_rational, nativeMixedPeriodCoordinates_rational,
    CMMixedHermitianForm.cmMixedHermitianForm_embedding]

omit [Fintype Place] in
theorem nativeMixedComponentChange_preserves_form
    (H : Matrix (Fin 3) (Fin 3) E) (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hq : ∀ p x y, Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom H
      (q p x) (q p y) = Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom H x y)
    (x y : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    nativeMixedHermitianForm E A e H (nativeMixedComponentChange E A σ hσ e q x)
        (nativeMixedComponentChange E A σ hσ e q y) =
      nativeMixedHermitianForm E A e H x y := by
  change CMMixedHermitianForm.cmMixedHermitianForm H (nativeMixedPeriodCoordinates E A e
    (nativeMixedComponentChange E A σ hσ e q x))
    (nativeMixedPeriodCoordinates E A e (nativeMixedComponentChange E A σ hσ e q y)) = _
  rw [nativeMixedComponentChange_coordinates, nativeMixedComponentChange_coordinates]
  exact (MixedFromComplexComponents.cmMixedOfComplexComponents_isometry_iff σ hσ H q).mpr hq _ _

omit [Fintype Place] in
theorem nativeMixedComponentChange_preserves_trace
    (H : Matrix (Fin 3) (Fin 3) E) (ξ : E)
    (B : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] ℝ)
    (hB : ∀ x y : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A,
      B x.val y.val = (Algebra.trace ℚ E
        (ξ * Datum.RankThreePELDatum.matrixHermitian H (e x) (e y)) : ℝ))
    (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hq : ∀ p x y, Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom H
      (q p x) (q p y) = Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom H x y)
    (x y : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    B (nativeMixedComponentChange E A σ hσ e q x)
      (nativeMixedComponentChange E A σ hσ e q y) = B x y := by
  have h : B = (nativeMixedHermitianForm E A e H).compr₂ (mixedTraceFunctional E ξ) := by
    apply Real.PeriodBilinearExt.realPeriodBilinear_ext A
    intro v w
    change B v.val w.val = mixedTraceFunctional E ξ (nativeMixedHermitianForm E A e H v.val w.val)
    rw [nativeMixedHermitianForm_rational, mixedTraceFunctional_embedding]
    exact hB v w
  rw [h]
  change mixedTraceFunctional E ξ
    (nativeMixedHermitianForm E A e H (nativeMixedComponentChange E A σ hσ e q x)
      (nativeMixedComponentChange E A σ hσ e q y)) = _
  rw [nativeMixedComponentChange_preserves_form E A σ hσ e H q hq]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MixedPeriodCoordinates
