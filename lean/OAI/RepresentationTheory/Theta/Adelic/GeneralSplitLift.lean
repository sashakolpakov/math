import OAI.RepresentationTheory.Theta.Adelic.GeneralSplitContinuous
import OAI.RepresentationTheory.Theta.Adelic.ContinuousLevi
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicCoverTopology
import OAI.RepresentationTheory.Theta.Adelic.CircleSmoothness
import OAI.RepresentationTheory.Theta.Adelic.FrameChange
import OAI.RepresentationTheory.Weil.Local.LocalGenerators

/-! # General Split Lift -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeneralSplitLift

noncomputable section

/-! A continuous splitting of the full split unitary pair in every rank
and every characteristic-zero local field. The actual operator is the
positive Levi substitution twisted by the two prescribed determinant
characters; the chosen tensor frame is changed by an actual oscillator. -/

open OAI.RepresentationTheory.Weil.Local.LocalGenerators.Construction
open OAI.RepresentationTheory.Theta.Adelic.GeneralSplitFrame OAI.RepresentationTheory.Theta.Adelic.GeneralSplitTensorAction OAI.RepresentationTheory.Theta.Adelic.GeneralSplitCharacter
open OAI.RepresentationTheory.Theta.Adelic.GeneralSplitContinuous OAI.RepresentationTheory.Theta.Adelic.ContinuousLevi OAI.RepresentationTheory.Theta.Adelic.FrameChange

variable {k : Type} [NormedField k] [CharZero k] [CompleteSpace k] [LocallyCompactSpace k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {d : k}
variable (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0) (n m : ℕ)
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
variable (χV χW : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* Circle)

def pairCharacter : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) →ₜ* Circle where
  toFun g := GeneralSplitContinuous.continuousUnitaryCharacter r hr hr0 H χW g.1 *
    GeneralSplitContinuous.continuousUnitaryCharacter r hr hr0 K χV g.2
  map_one' := by
    change GeneralSplitContinuous.continuousUnitaryCharacter r hr hr0 H χW 1 * GeneralSplitContinuous.continuousUnitaryCharacter r hr hr0 K χV 1 = 1
    simp only [map_one, mul_one]
  map_mul' g h := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    ac_rfl
  continuous_toFun :=
    ((GeneralSplitContinuous.continuousUnitaryCharacter r hr hr0 H χW).continuous.comp continuous_fst).mul
      ((GeneralSplitContinuous.continuousUnitaryCharacter r hr hr0 K χV).continuous.comp continuous_snd)

variable (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)

def stableLift : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ := by
  let : IsTopologicalGroup (Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ) :=
    IntrinsicCoverTopology.Intrinsic.localCover_isTopologicalGroup k (n * m) ψ
  let c := pairCharacter r hr hr0 n m H K χV χW
  let L := (ContinuousLevi.continuousLevi hnd ψ).comp (GeneralSplitContinuous.continuousLinearPair r hr hr0 n m H K)
  refine {
    toFun := fun g => Weil.AdelicSplitting.Oscillator.Construction.localScalar k (n * m) ψ (c g) * L g
    map_one' := by simp only [map_one, mul_one]
    map_mul' := ?_
    continuous_toFun := ((CircleSmoothness.localScalar_continuous k (n * m) ψ).comp c.continuous).mul L.continuous }
  intro g h
  rw [map_mul, map_mul, map_mul]
  have hc := Weil.AdelicSplitting.Oscillator.Construction.localScalar_central k (n * m) ψ (c h) (L g)
  calc
    _ = Weil.AdelicSplitting.Oscillator.Construction.localScalar k (n * m) ψ (c g) * (Weil.AdelicSplitting.Oscillator.Construction.localScalar k (n * m) ψ (c h) * L g) * L h := by
      simp only [mul_assoc]
    _ = _ := by rw [hc.eq]; simp only [mul_assoc]

theorem stableLift_projection (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) :
    Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ (stableLift r hr hr0 n m H K χV χW hnd ψ g) =
      Weil.Local.Generators.Construction.leviSymplectic (GeneralSplitTensorAction.linearPair r hr hr0 n m H K g) := by
  change Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ
    (Weil.AdelicSplitting.Oscillator.Construction.localScalar k (n * m) ψ (pairCharacter r hr hr0 n m H K χV χW g) *
      Weil.AdelicSplitting.NormalizationLevi.Construction.localLeviHom (n * m) ψ (GeneralSplitTensorAction.linearPair r hr hr0 n m H K g)) = _
  rw [map_mul, Weil.AdelicSplitting.Oscillator.Construction.localProjection_scalar, one_mul]
  rfl

theorem stableLift_operator (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (n * m)) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k (n * m)) :
    (Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (stableLift r hr hr0 n m H K χV χW hnd ψ g) f).val x =
      (pairCharacter r hr hr0 n m H K χV χW g : ℂ) *
        ((Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k (GeneralSplitTensorAction.linearPair r hr hr0 n m H K g))))⁻¹ : ℂ) *
          f.val ((GeneralSplitTensorAction.linearPair r hr hr0 n m H K g)⁻¹.val.mulVec x) := by
  change (Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ
    (Weil.AdelicSplitting.Oscillator.Construction.localScalar k (n * m) ψ (pairCharacter r hr hr0 n m H K χV χW g) *
      Weil.AdelicSplitting.NormalizationLevi.Construction.localLeviHom (n * m) ψ (GeneralSplitTensorAction.linearPair r hr hr0 n m H K g)) f).val x = _
  rw [map_mul, LinearEquiv.mul_apply, Weil.AdelicSplitting.Oscillator.Construction.localOperator_scalar]
  change (pairCharacter r hr hr0 n m H K χV χW g : ℂ) *
    ((Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ (GeneralSplitTensorAction.linearPair r hr hr0 n m H K g)).val.2 f).val x = _
  rw [Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator_apply, mul_assoc]

theorem exists_split_lift (hnm : 0 < n * m)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H.val K.val)
    (hc : Continuous ψ) (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1) :
    ∃ s : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ,
      (∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ (s g) = Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P g) ∧
      ∃ w : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ,
        Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ w = FrameChange.frameChange P (GeneralSplitFrame.splitFrame r hr hr0 n m H K hH hK) ∧
        ∀ g, w * s g * w⁻¹ = stableLift r hr hr0 n m H K χV χW hnd ψ g := by
  let : IsTopologicalGroup (Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ) :=
    IntrinsicCoverTopology.Intrinsic.localCover_isTopologicalGroup k (n * m) ψ
  let B := FrameChange.frameChange P (GeneralSplitFrame.splitFrame r hr hr0 n m H K hH hK)
  obtain ⟨hsurj, _⟩ := Weil.Local.LocalGenerators.Construction.localField_metaplectic_generators hnd (n * m) hnm ψ hc hu hn
  obtain ⟨W, hW⟩ := hsurj B
  let w : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ := W.val
  have hw : Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ w = B := hW
  let S := stableLift r hr hr0 n m H K χV χW hnd ψ
  let s : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ :=
    { (MulAut.conj w⁻¹).toMonoidHom.comp S.toMonoidHom with
      continuous_toFun := (continuous_const.mul S.continuous).mul continuous_const }
  have hs (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) : s g = w⁻¹ * S g * w := by
    change w⁻¹ * S g * (w⁻¹)⁻¹ = _
    rw [inv_inv]
  refine ⟨s, ?_, w, hw, ?_⟩
  · intro g
    rw [hs, map_mul, map_mul, map_inv, hw]
    rw [stableLift_projection, ← GeneralSplitTensorAction.splitFrame_action r hr hr0 n m H K hH hK,
      ← FrameChange.frameChange_conjugates P (GeneralSplitFrame.splitFrame r hr hr0 n m H K hH hK)]
    change B⁻¹ * (B * _ * B⁻¹) * B = _
    group
  · intro g
    rw [hs]
    change w * (w⁻¹ * S g * w) * w⁻¹ = S g
    group

end

end OAI.RepresentationTheory.Theta.Adelic.GeneralSplitLift
