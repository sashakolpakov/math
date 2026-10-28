import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Euler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerEulerScaling
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.SectionPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers

/-! # Euler Sequence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The Euler sequence of a fixed positive graph-bundle power has the actual dilation law and agrees eventually with every intrinsic section polynomial of that power. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

def PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEulerSequence (r m : ℕ) : ℚ :=
  (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom
    (A.graphBundle.tensorPower (r * m)).sheaf : ℚ)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEulerSequence_scaling [IsAlgClosed K] [NeZero N] (hNk : (N : K) ≠ 0) (r m : ℕ) :
    A.graphPowerEulerSequence r (m * (N * N)) =
      ((N * N : ℕ) : ℚ) ^ g * A.graphPowerEulerSequence r m := by
  have hs := PoincareGraph.PowerEulerScaling.poincareGraphBundle_tensorPowers_euler_scaling A.dual A.level
    A.polarization.isogeny.hom hNk (r * m)
  have hc := congrArg (fun z : ℤ => (z : ℚ)) hs
  have hw : ((N * N : ℕ) : ℚ) ^ g = (N : ℚ) ^ (2 * g) := by
    rw [Nat.cast_mul, ← pow_two, ← pow_mul]
  rw [hw]
  simpa only [PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEulerSequence, PolarizationData.PolarizedAbelianWithFullLevel.graphBundle, Nat.mul_assoc,
    Int.cast_mul, Int.cast_pow, Int.cast_natCast] using hc

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEulerSequence_eventual
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(Spec (.of K), ⊤)))
    (r : ℕ) (hr : 0 < r) (P : Polynomial ℚ)
    (hP : (A.graphBundle.tensorPower r).HasSectionHilbertPolynomial A.abelian.scheme.hom P) :
    ∃ b : ℕ, ∀ m, b ≤ m → P.eval (m : ℚ) = A.graphPowerEulerSequence r m := by
  obtain ⟨b, hb⟩ := hP
  refine ⟨max b 1, fun m hm => ?_⟩
  have hm0 : 0 < m := (le_max_right b 1).trans hm
  have hdim := (hb m ((le_max_left b 1).trans hm)).2
  have hs := (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso A.abelian.scheme.hom
    (A.graphBundle.tensorPowerComposeIso m r)).finrank_eq
  have he := congrArg (fun z : ℤ => (z : ℚ))
    (A.graphBundle_positivePower_euler_eq_sections hN hunit (m * r) (Nat.mul_pos hm0 hr))
  simp only [Int.cast_natCast] at he
  calc
    P.eval (m : ℚ) =
        (Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
          ((A.graphBundle.tensorPower r).tensorPower m).sheaf) : ℚ) := hdim
    _ = (Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
          (A.graphBundle.tensorPower (m * r)).sheaf) : ℚ) :=
      congrArg (fun n : ℕ => (n : ℚ)) hs.symm
    _ = A.graphPowerEulerSequence r m := by
      simpa only [PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEulerSequence, Nat.mul_comm m r] using he.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
