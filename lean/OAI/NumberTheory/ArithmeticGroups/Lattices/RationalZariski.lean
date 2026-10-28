import OAI.NumberTheory.ArithmeticGroups.Lattices.LeftTranslation
import OAI.NumberTheory.ArithmeticGroups.Lattices.Zariski

/-! # Rational Zariski -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RationalZariski.Construction

noncomputable section

/-! The Zariski topology on rational points, using coordinate
polynomials over the base field. -/

open scoped Classical
open _root_.MvPolynomial _root_.Topology _root_.TopologicalSpace Set

def rationalPrime {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (g : G.RationalPoints) :
    PrimeSpectrum (Algebraic.CoordinatePolynomial n k) :=
  ⟨RingHom.ker (Algebraic.evaluateMatrix (RingHom.id k) g.val), RingHom.ker_isPrime _⟩

@[instance_reducible] def rationalZariskiTopology {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : TopologicalSpace G.RationalPoints :=
  TopologicalSpace.induced (rationalPrime G) inferInstance

variable {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)

local instance rationalPointsTopology : TopologicalSpace G.RationalPoints := rationalZariskiTopology G

theorem rational_zariski_noetherian : NoetherianSpace G.RationalPoints :=
  (show IsInducing (rationalPrime G) from ⟨rfl⟩).noetherianSpace

theorem continuous_rationalPrime : Continuous (rationalPrime G) := continuous_induced_dom

theorem rational_polynomial_zero_closed (p : Algebraic.CoordinatePolynomial n k) :
    IsClosed {g : G.RationalPoints | Algebraic.evaluateMatrix (RingHom.id k) g.val p = 0} := by
  convert (PrimeSpectrum.isClosed_zeroLocus {p}).preimage (continuous_rationalPrime G) using 1
  ext g
  simp [PrimeSpectrum.mem_zeroLocus, rationalPrime]

theorem rational_polynomial_map_continuous (f : G.RationalPoints → G.RationalPoints)
    (P : Fin n × Fin n → Algebraic.CoordinatePolynomial n k)
    (hP : ∀ x i j, (f x).val i j = Algebraic.evaluateMatrix (RingHom.id k) x.val (P (i, j))) :
    Continuous f := by
  have heval (x : G.RationalPoints) (p : Algebraic.CoordinatePolynomial n k) :
      Algebraic.evaluateMatrix (RingHom.id k) (f x).val p =
        Algebraic.evaluateMatrix (RingHom.id k) x.val (aeval P p) := by
    induction p using MvPolynomial.induction_on with
    | C c => simp [Algebraic.evaluateMatrix]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p ij hp =>
        rcases ij with ⟨i, j⟩
        simp only [map_mul, hp, aeval_X]
        rw [show Algebraic.evaluateMatrix (RingHom.id k) (f x).val (X (i, j)) = (f x).val i j from
          by simp [Algebraic.evaluateMatrix], hP]
  have hprime : rationalPrime G ∘ f =
      PrimeSpectrum.comap (aeval P).toRingHom ∘ rationalPrime G := by
    funext x
    apply PrimeSpectrum.ext
    ext p
    change Algebraic.evaluateMatrix (RingHom.id k) (f x).val p = 0 ↔
      Algebraic.evaluateMatrix (RingHom.id k) x.val (aeval P p) = 0
    rw [heval]
  apply continuous_induced_rng.mpr
  change Continuous (rationalPrime G ∘ f)
  rw [hprime]
  exact (PrimeSpectrum.continuous_comap _).comp (continuous_rationalPrime G)

theorem rational_right_mul_continuous (g : G.RationalPoints) :
    Continuous (fun x : G.RationalPoints => x * g) := by
  apply rational_polynomial_map_continuous G _
    (fun ij => ∑ l, X (ij.1, l) * C (g.val l ij.2))
  intro x i j
  simp [Algebraic.evaluateMatrix, Matrix.mul_apply]

theorem rational_left_mul_continuous (g : G.RationalPoints) :
    Continuous (fun x : G.RationalPoints => g * x) := by
  apply rational_polynomial_map_continuous G _
    (fun ij => ∑ l, C (g.val ij.1 l) * X (l, ij.2))
  intro x i j
  simp [Algebraic.evaluateMatrix, Matrix.mul_apply]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RationalZariski.Construction
