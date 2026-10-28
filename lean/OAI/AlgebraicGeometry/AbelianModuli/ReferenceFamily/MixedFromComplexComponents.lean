import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMSelectedMixed
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ScalarLinearComponents

/-! # Mixed From Complex Components -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MixedFromComplexComponents

noncomputable section

section

/-! The actual mixed-coefficient-linear equivalence transports to
the original selected product algebra and therefore yields actual
complex-linear component maps with exact original-coordinate intertwining. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

variable {E : Type} {Place : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [IsCMField E]
  (σ : Place → E →ₐ[ℚ] ℂ)
  (hσ : Function.Bijective
    (fun p : Place × Bool => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))

local notation "A" => mixedSpace E
local notation "V" => Fin 3 → A
local notation "W" => Place → OAI.Geometry.ComplexBall.PrescribedSignsB.Vec
local notation "S" => Place → ℂ
local notation "Φ" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMSelectedMixed.cmSelectedMixedCoordinates σ hσ
local notation "e" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMSelectedMixed.cmSelectedMixedScalarAlgebraEquiv σ hσ

theorem cmSelectedMixedCoordinates_smul (a : A) (x : V) :
    Φ (a • x) = e a • Φ x := by
  ext p i
  change e (a * x i) p = e a p * e (x i) p
  rw [map_mul]
  rfl

theorem cmSelectedMixedCoordinates_symm_smul (a : S) (x : W) :
    (Φ).symm (a • x) = (e).symm a • (Φ).symm x := by
  apply (Φ).injective
  rw [(Φ).apply_symm_apply, cmSelectedMixedCoordinates_smul,
    (e).apply_symm_apply, (Φ).apply_symm_apply]

def cmSelectedScalarLinearTransport (f : V ≃ₗ[A] V) : W ≃ₗ[S] W where
  toEquiv := ((Φ).symm.trans ((f.restrictScalars ℝ).trans Φ)).toEquiv
  map_add' := ((Φ).symm.trans ((f.restrictScalars ℝ).trans Φ)).map_add
  map_smul' a x := by
    change Φ (f ((Φ).symm (a • x))) = a • Φ (f ((Φ).symm x))
    rw [cmSelectedMixedCoordinates_symm_smul, f.map_smul,
      cmSelectedMixedCoordinates_smul, (e).apply_symm_apply]

def cmSelectedComplexComponent (f : V ≃ₗ[A] V) (p : Place) : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec :=
  Product.ScalarLinearComponents.piScalarLinearComponent (cmSelectedScalarLinearTransport σ hσ f) p

theorem cmSelectedComplexComponent_intertwines (f : V ≃ₗ[A] V) (x : V) (p : Place) :
    Φ (f x) p = cmSelectedComplexComponent σ hσ f p (Φ x p) := by
  have h := Product.ScalarLinearComponents.piScalarLinearComponent_apply (cmSelectedScalarLinearTransport σ hσ f) p (Φ x)
  change Φ (f ((Φ).symm (Φ x))) p = cmSelectedComplexComponent σ hσ f p (Φ x p) at h
  rw [(Φ).symm_apply_apply] at h
  exact h

theorem cmSelectedComplexComponent_isometry_iff
    (H : Matrix (Fin 3) (Fin 3) E) (f : V ≃ₗ[A] V) :
    (∀ x y, CMMixedHermitianForm.cmMixedHermitianForm H (f x) (f y) = CMMixedHermitianForm.cmMixedHermitianForm H x y) ↔
      ∀ p x y, Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom H
        (cmSelectedComplexComponent σ hσ f p x) (cmSelectedComplexComponent σ hσ f p y) =
          Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom H x y :=
  CMSelectedMixed.cmSelectedMixedHermitian_isometry_iff σ hσ H (f.restrictScalars ℝ)
    (cmSelectedComplexComponent σ hσ f) (cmSelectedComplexComponent_intertwines σ hσ f)

end

/-! Component complex-linear maps construct an actual mixed-algebra
linear equivalence in the original selected coordinates. This is the
inverse of the proved component extraction, with exact Hermitian behavior. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

variable {E : Type} {Place : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [IsCMField E] [Fintype Place]
  (σ : Place → E →ₐ[ℚ] ℂ)
  (hσ : Function.Bijective
    (fun p : Place × Bool => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))

local notation "A" => mixedSpace E
local notation "V" => Fin 3 → A
local notation "W" => Place → OAI.Geometry.ComplexBall.PrescribedSignsB.Vec
local notation "S" => Place → ℂ
local notation "Φ" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMSelectedMixed.cmSelectedMixedCoordinates σ hσ
local notation "e" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMSelectedMixed.cmSelectedMixedScalarAlgebraEquiv σ hσ

def cmMixedScalarLinearOfSelected (f : W ≃ₗ[S] W) : V ≃ₗ[A] V where
  toEquiv := ((Φ).trans ((f.restrictScalars ℝ).trans (Φ).symm)).toEquiv
  map_add' := ((Φ).trans ((f.restrictScalars ℝ).trans (Φ).symm)).map_add
  map_smul' a x := by
    change (Φ).symm (f (Φ (a • x))) = a • (Φ).symm (f (Φ x))
    rw [cmSelectedMixedCoordinates_smul, f.map_smul,
      cmSelectedMixedCoordinates_symm_smul, (e).symm_apply_apply]

def cmMixedOfComplexComponents (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) : V ≃ₗ[A] V :=
  cmMixedScalarLinearOfSelected σ hσ (Product.ScalarLinearComponents.piComponentsScalarLinearEquiv q)

omit [Fintype Place] in
theorem cmMixedOfComplexComponents_intertwines
    (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (x : V) (p : Place) :
    Φ (cmMixedOfComplexComponents σ hσ q x) p = q p (Φ x p) := by
  change Φ ((Φ).symm (Product.ScalarLinearComponents.piComponentsScalarLinearEquiv q (Φ x))) p = _
  rw [(Φ).apply_symm_apply]
  rfl

omit [Fintype Place] in
theorem cmMixedOfComplexComponents_reconstructs (f : V ≃ₗ[A] V) :
    cmMixedOfComplexComponents σ hσ (cmSelectedComplexComponent σ hσ f) = f := by
  apply LinearEquiv.ext
  intro x
  apply (Φ).injective
  ext p
  rw [cmMixedOfComplexComponents_intertwines, cmSelectedComplexComponent_intertwines]

omit [Fintype Place] in
theorem cmMixedOfComplexComponents_isometry_iff
    (H : Matrix (Fin 3) (Fin 3) E) (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) :
    (∀ x y, CMMixedHermitianForm.cmMixedHermitianForm H (cmMixedOfComplexComponents σ hσ q x)
      (cmMixedOfComplexComponents σ hσ q y) = CMMixedHermitianForm.cmMixedHermitianForm H x y) ↔
      ∀ p x y, Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom H (q p x) (q p y) =
        Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom H x y :=
  CMSelectedMixed.cmSelectedMixedHermitian_isometry_iff σ hσ H
    ((cmMixedOfComplexComponents σ hσ q).restrictScalars ℝ) q
    (cmMixedOfComplexComponents_intertwines σ hσ q)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MixedFromComplexComponents
