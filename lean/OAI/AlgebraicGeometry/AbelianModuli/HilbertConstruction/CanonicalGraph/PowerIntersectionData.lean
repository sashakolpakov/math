import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.IntegerEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Quadratic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # Power Intersection Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every actual tensor power of the canonical graph bundle has the
integer Euler monomial with its own Euler coefficient and the quadratic
multiplication pullback class needed for the intersection bound. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundlePower_integerPower_euler (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (k : ℕ) (z : ℤ) :
    LineBundle.EulerShifts.lineBundleClassEuler A.abelian.scheme.hom (Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower k) ^ z) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower k).sheaf * z ^ g := by
  have hc : Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower k) ^ z =
      Line.Bundles.LineBundle.classOf A.graphBundle ^ ((k : ℤ) * z) := by
    rw [Line.Bundles.LineBundle.classOf_tensorPower, zpow_mul, zpow_natCast]
  rw [hc, A.graphBundle_integerPower_euler hN hNk,
    A.graphBundle_tensorPower_euler_overField hN hNk, mul_pow]
  ring

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundlePower_multiplication_class (k n : ℕ) :
    Line.Bundles.LineBundle.classOf ((A.graphBundle.tensorPower k).pullback (A.abelian.multiplication n).left) =
      Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower k) ^ ((n : ℤ) ^ 2) := by
  have hbase : Line.Bundles.LineBundle.classOf (A.graphBundle.pullback (A.abelian.multiplication n).left) =
      Line.Bundles.LineBundle.classOf A.graphBundle ^ (n * n) :=
    (Quotient.sound (A.graphBundle_multiplication_iso n)).trans (Line.Bundles.LineBundle.classOf_tensorPower _ _)
  have hpull : Line.Bundles.LineBundle.classOf ((A.graphBundle.tensorPower k).pullback (A.abelian.multiplication n).left) =
      Line.Bundles.LineBundle.classOf (A.graphBundle.pullback (A.abelian.multiplication n).left) ^ k :=
    have he : Line.Bundles.LineBundle.classOf ((A.graphBundle.tensorPower k).pullback (A.abelian.multiplication n).left) =
        Line.Bundles.LineBundle.classOf ((A.graphBundle.pullback (A.abelian.multiplication n).left).tensorPower k) :=
      Quotient.sound ⟨Line.Bundles.LineBundle.powerBaseChangeIso (A.abelian.multiplication n).left A.graphBundle k⟩
    he.trans (Line.Bundles.LineBundle.classOf_tensorPower _ _)
  rw [hpull, hbase, Line.Bundles.LineBundle.classOf_tensorPower,
    show (n : ℤ) ^ 2 = ((n * n : ℕ) : ℤ) by simp only [pow_two, Nat.cast_mul], zpow_natCast,
    ← pow_mul, ← pow_mul, Nat.mul_comm (n * n) k]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
