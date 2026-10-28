import OAI.RepresentationTheory.Theta.Adelic.ComplexSymplecticPairing
import OAI.RepresentationTheory.Theta.Adelic.GeometricConjugation
import OAI.RepresentationTheory.Theta.Adelic.HodgeMetricPositivity

/-! # Positive Geometric Pairing -/

namespace OAI.RepresentationTheory.Theta.Adelic.PositiveGeometricPairing

noncomputable section

/-! Isotropy and positivity of the actual Hodge frame for the
complexified native trace symplectic pairing. -/

open scoped Classical _root_.NumberField ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.GeometricTracePairing
open OAI.RepresentationTheory.Theta.Adelic.GeometricConjugation OAI.RepresentationTheory.Theta.Adelic.HodgeMetricPositivity

theorem paired_metric_scalar (η x y : ℂ) (hη : η.im = 0) :
    2 * ((η * conj y * y - η * conj x * x) / (2 * Complex.I)).im =
      η.re * (Complex.normSq x - Complex.normSq y) := by
  norm_num [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.normSq_apply, hη]
  ring

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

theorem geometric_pairing_conj_energy (w : BallGeometryData.ComplexPhase A) :
    2 * (GeometricTracePairing.geometricPairing A (GeometricConjugation.geometricConj A w) w).im = HodgeMetricPositivity.geometricEnergy A w := by
  simp only [GeometricTracePairing.geometricPairing, Complex.im_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro ij _
  exact paired_metric_scalar (ComplexPhaseCoordinates.tensorDualSign A (v, ij)) ((w v).1 ij) ((w v).2 ij)
    (GeometricTracePairing.tensorDualSign_im A (v, ij))

theorem geometric_frame_isotropic (z : BallNatural.Ball) (a b : BallGeometryData.FrameIndex A → ℂ) :
    GeometricTracePairing.geometricPairing A (BallGeometryData.geometricFrame A z a) (BallGeometryData.geometricFrame A z b) = 0 := by
  unfold GeometricTracePairing.geometricPairing
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v = A.distinguished
  · subst v
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    simp [Fin.sum_univ_succ, BallGeometryData.geometricFrame, DeterminantCoordinates.lineVector, DeterminantCoordinates.annihilatorVector]
    ring
  · apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ _
    by_cases hp : A.positive v j <;> simp [BallGeometryData.geometricFrame, hv, hp]

theorem geometric_frame_positive (z : BallNatural.Ball) (a : BallGeometryData.FrameIndex A → ℂ) (ha : a ≠ 0) :
    0 < (GeometricTracePairing.geometricPairing A (GeometricConjugation.geometricConj A (BallGeometryData.geometricFrame A z a))
      (BallGeometryData.geometricFrame A z a)).im := by
  have h := HodgeMetricPositivity.geometricFrame_energy_pos A z a ha
  rw [← geometric_pairing_conj_energy] at h
  linarith

end

end OAI.RepresentationTheory.Theta.Adelic.PositiveGeometricPairing
