import OAI.RepresentationTheory.Weil.UnitarySplitting.CoordinateChange
import OAI.RepresentationTheory.Weil.UnitarySplitting.HeisenbergStability

/-! # Fourier Covariance -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.FourierCovariance.Construction

noncomputable section

/-! Fourier covariance with the Weyl operators, before Fourier inversion
or unitarity has been established. -/

open _root_.MeasureTheory
open scoped BigOperators

def phasePosition {F : Type} {d : ℕ} (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : Local.FunctionsMetaplectic.Construction.Position F d :=
  fun i => v (Sum.inl i)

def phaseMomentum {F : Type} {d : ℕ} (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : Local.FunctionsMetaplectic.Construction.Position F d :=
  fun i => v (Sum.inr i)

def fourierPhaseRotation {F : Type} [Neg F] {d : ℕ} (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : Local.FunctionsMetaplectic.Construction.PhaseSpace F d :=
  Sum.elim (phaseMomentum v) (-phasePosition v)

theorem heisenbergFunction_dot {F : Type} [Field F] {d : ℕ}
    (ψ : AddChar F ℂ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position F d) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f x = ψ (Local.FunctionsMetaplectic.Construction.dot (phaseMomentum v)
      (x - (2 : F)⁻¹ • phasePosition v)) * f (x - phasePosition v) := by
  unfold Local.FunctionsMetaplectic.Construction.heisenbergFunction Local.FunctionsMetaplectic.Construction.dot phasePosition phaseMomentum
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  rw [mul_comm (2 : F)⁻¹]

theorem fourierIntegral_heisenberg
    {F : Type} [NormedField F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (ψ : AddChar F ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [μ.IsAddHaarMeasure]
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) =
      Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (fourierPhaseRotation v) (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) := by
  funext x
  rw [heisenbergFunction_dot]
  change _ = ψ (Local.FunctionsMetaplectic.Construction.dot (-phasePosition v) (x - (2 : F)⁻¹ • phaseMomentum v)) *
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f (x - phaseMomentum v)
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  rw [← integral_add_right_eq_self
    (fun y => Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f y * ψ (-Local.FunctionsMetaplectic.Construction.dot x y)) (phasePosition v)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [heisenbergFunction_dot, add_sub_cancel_right]
    have hphase : Local.FunctionsMetaplectic.Construction.dot (phaseMomentum v) (y + phasePosition v - (2 : F)⁻¹ • phasePosition v) -
        Local.FunctionsMetaplectic.Construction.dot x (y + phasePosition v) =
      Local.FunctionsMetaplectic.Construction.dot (-phasePosition v) (x - (2 : F)⁻¹ • phaseMomentum v) - Local.FunctionsMetaplectic.Construction.dot (x - phaseMomentum v) y := by
      simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
        smul_eq_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    calc
      _ = ψ (Local.FunctionsMetaplectic.Construction.dot (phaseMomentum v)
          (y + phasePosition v - (2 : F)⁻¹ • phasePosition v) - Local.FunctionsMetaplectic.Construction.dot x (y + phasePosition v)) * f y := by
        simp only [sub_eq_add_neg, ψ.map_add_eq_mul]
        ring
      _ = _ := by
        rw [hphase]
        simp only [sub_eq_add_neg, ψ.map_add_eq_mul]
        ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.FourierCovariance.Construction
