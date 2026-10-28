import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement

/-! # Intrinsic Symplectic Comparison -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicSymplecticComparison.Intrinsic

noncomputable section

/-! The native complex phase transport preserves the symplectic form,
as a consequence of its rational identification. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicComplexTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.Intrinsic

theorem linear_ext_rational {I V : Type} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Module ℂ V] (f g : (I → ℂ) →ₗ[ℂ] V)
    (h : ∀ x : I → ℚ, f (fun i => (x i : ℂ)) = g (fun i => (x i : ℂ))) : f = g := by
  apply (Pi.basisFun ℂ I).ext
  intro i
  have hc : (fun j : I => ((Pi.single i (1 : ℚ) : I → ℚ) j : ℂ)) =
      (Pi.single i (1 : ℂ) : I → ℂ) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  have he := h (Pi.single i 1)
  rw [hc] at he
  simpa only [Pi.basisFun_apply] using he

def pairingBilinear (k I : Type) [Field k] [Fintype I] :
    ((I ⊕ I) → k) →ₗ[k] ((I ⊕ I) → k) →ₗ[k] k :=
  LinearMap.mk₂ k Adelic.DataTheta.standardPairing
    (by
      intro x y z
      simp only [Adelic.DataTheta.standardPairing, Pi.add_apply, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro c x y
      simp only [Adelic.DataTheta.standardPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro x y z
      simp only [Adelic.DataTheta.standardPairing, Pi.add_apply, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro c x y
      simp only [Adelic.DataTheta.standardPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)

theorem pairing_cast {I : Type} [Fintype I] (x y : (I ⊕ I) → ℚ) :
    Adelic.DataTheta.standardPairing (fun i => (x i : ℂ)) (fun i => (y i : ℂ)) =
      ((Adelic.DataTheta.standardPairing x y : ℚ) : ℂ) := by
  simp only [Adelic.DataTheta.standardPairing, Rat.cast_sum, Rat.cast_sub, Rat.cast_mul]

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁} {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

theorem complexPhaseChange_pairing (h₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁)
    (h₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hB : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (x y : (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) → ℂ) :
    Adelic.DataTheta.standardPairing (IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B x) (IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B y) =
      Adelic.DataTheta.standardPairing x y := by
  let f := (pairingBilinear ℂ _).compl₁₂ (IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B).toLinearMap
    (IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B).toLinearMap
  have he : f = pairingBilinear ℂ _ := by
    apply linear_ext_rational
    intro u
    apply linear_ext_rational
    intro v
    change Adelic.DataTheta.standardPairing (IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B (fun i => (u i : ℂ)))
      (IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B (fun i => (v i : ℂ))) =
        Adelic.DataTheta.standardPairing (fun i => (u i : ℂ)) (fun i => (v i : ℂ))
    rw [IntrinsicCoordinateAgreement.Intrinsic.complexPhaseChange_rational B₁ B₂ B h₁ h₂ hB u,
      IntrinsicCoordinateAgreement.Intrinsic.complexPhaseChange_rational B₁ B₂ B h₁ h₂ hB v,
      pairing_cast, pairing_cast, IntrinsicPhaseTransport.Intrinsic.rationalPhaseChange_pairing B₁ B₂ B h₁ h₂ hB]
  exact congrArg (fun b => b x y) he

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicSymplecticComparison.Intrinsic
