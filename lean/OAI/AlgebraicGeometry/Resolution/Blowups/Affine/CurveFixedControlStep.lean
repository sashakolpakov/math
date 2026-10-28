import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.FixedControlDrop
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.IntrinsicStep

/-! # Curve Fixed Control Step -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveFixedControlStep.Construction

noncomputable section

/-! Fixed-control intrinsic-center reduction on arbitrary smooth affine curve algebras. -/

open _root_.CategoryTheory

universe u

variable (k : Type u) {R : Type u} [CommRing R]
  [Field k] [IsAlgClosed k] [Algebra k R] [Algebra ℚ R]
  [IsNoetherianRing R] [Algebra.Smooth k R]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- The original tangent ideal supplies a smooth permissible center and
strict order reduction at the unchanged positive control on every actual
chart. No integrality assumption or chosen global coordinates are needed. -/
theorem affine_curve_fixed_control_step (hd : ringKrullDim R ≤ 1)
    (J : Ideal R) (n b : ℕ) (hb : 0 < b) (hbn : b ≤ n + 1)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (n + 1) = ⊤) :
    let T := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
    J ≤ T ^ b ∧ Algebra.Smooth k (R ⧸ T) ∧ IsIso (ReesGrading.Construction.affineBlowupToSpec T) ∧
      ∀ a : T, Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform T J b a) n = ⊤ := by
  let T := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  obtain ⟨hperm, hsmooth, hπ, _⟩ := Curve.IntrinsicStep.Construction.curve_intrinsic_tangent_step k hd J n hbound
  let : IsIso (ReesGrading.Construction.affineBlowupToSpec T) := hπ
  have hpermb : J ≤ T ^ b := hperm.trans (Ideal.pow_le_pow_right hbn)
  exact ⟨hpermb, hsmooth, hπ,
    fun a => FixedControlDrop.Construction.isIso_blowup_fixed_control_drop k T J a n b hb rfl hpermb hbound⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveFixedControlStep.Construction
