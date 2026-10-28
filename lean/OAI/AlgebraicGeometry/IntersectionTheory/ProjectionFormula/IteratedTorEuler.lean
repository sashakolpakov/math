import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IteratedTorBounds
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ConvergenceEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EulerWeights
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Permutation

/-! # Iterated Tor Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IteratedTorEuler

noncomputable section

/-! Alternating sums of iterated native Tor lengths are computed by the
actual total tensor complex. Interchanging the two resolutions gives
the same Euler characteristic. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EulerWeights

variable (R : Type) [CommRing R]

def euler (L M N : ModuleCat.{0} R) (a b : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), (-1 : ℚ) ^ (i + j) *
    ExactLength.rationalLength R (((Tor (ModuleCat.{0} R) i).obj (((Tor (ModuleCat.{0} R) j).obj N).obj M)).obj L)

def total (L M N : ModuleCat.{0} R) (P : ProjectiveResolution M) (Q : ProjectiveResolution L) (c : ℕ) : ℚ :=
  ∑ n ∈ EulerWeights.degrees c, EulerWeights.sign n * ExactLength.rationalLength R
    ((HomologicalComplex.tensorObj (ChainToCochain.cochain R Q.complex)
      (((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj (ChainToCochain.cochain R P.complex))).homology n)

theorem page_sum (L M N : ModuleCat.{0} R) (P : ProjectiveResolution M) (Q : ProjectiveResolution L)
    (a b : ℕ) :
    (∑ pq ∈ Tensor.PageBounds.support a b, EulerWeights.sign (pq.1 + pq.2) * ExactLength.rationalLength R
      (((IteratedTorPage.spectralSequence R L M N P Q).page 3).X pq)) = euler R L M N a b := by
  unfold Tensor.PageBounds.support euler
  rw [Finset.sum_image (fun _ _ _ _ h => EulerWeights.position_injective h),
    Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (1 - 2 * (i : ℤ) - (j : ℤ)) + ((i : ℤ) - 1) = -(i : ℤ) - (j : ℤ) := by omega
  dsimp only
  rw [he, EulerWeights.sign_neg_sum]
  unfold ExactLength.rationalLength
  rw [(IteratedTorPage.iso R L M N P Q i j).toLinearEquiv.length_eq]

theorem total_eq (L M N : ModuleCat.{0} R) (P : ProjectiveResolution M) (Q : ProjectiveResolution L)
    (a b : ℕ) (hP : ∀ j, b < j → IsZero (P.complex.X j)) (hQ : ∀ i, a < i → IsZero (Q.complex.X i))
    (hlen : ∀ i, i ≤ a → ∀ j, j ≤ b →
      Module.length R (((Tor (ModuleCat.{0} R) i).obj (((Tor (ModuleCat.{0} R) j).obj N).obj M)).obj L) ≠ ⊤) :
    total R L M N P Q (a + b) = euler R L M N a b := by
  let A := ChainToCochain.cochain R Q.complex
  let K := ((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj (ChainToCochain.cochain R P.complex)
  have h := Tensor.ConvergenceEuler.euler_from_third_page R A K a
    (fun i hi => ChainToCochain.bounded R Q.complex a hQ i (Or.inl hi))
    (ChainToCochain.positive_zero R Q.complex)
    (Tensor.PageBounds.support a b) (EulerWeights.degrees (a + b))
    (IteratedTorBounds.supported R L M N P Q a b hP hQ)
    (IteratedTorBounds.finite R L M N P Q a b hlen)
    (EulerWeights.support_degrees a b) (EulerWeights.support_strip a b) EulerWeights.sign (fun r _ pq pq' h => EulerWeights.opposite r pq pq' h)
  exact h.trans (page_sum R L M N P Q a b)

theorem commute (L M N : ModuleCat.{0} R) (P : ProjectiveResolution M) (Q : ProjectiveResolution L)
    (a b : ℕ) (hP : ∀ j, b < j → IsZero (P.complex.X j)) (hQ : ∀ i, a < i → IsZero (Q.complex.X i))
    (hLM : ∀ i, i ≤ a → ∀ j, j ≤ b →
      Module.length R (((Tor (ModuleCat.{0} R) i).obj (((Tor (ModuleCat.{0} R) j).obj N).obj M)).obj L) ≠ ⊤)
    (hML : ∀ j, j ≤ b → ∀ i, i ≤ a →
      Module.length R (((Tor (ModuleCat.{0} R) j).obj (((Tor (ModuleCat.{0} R) i).obj N).obj L)).obj M) ≠ ⊤) :
    euler R L M N a b = euler R M L N b a := by
  rw [← total_eq R L M N P Q a b hP hQ hLM, ← total_eq R M L N Q P b a hQ hP hML]
  unfold total
  rw [Nat.add_comm b a]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  exact congrArg (fun x : ℕ∞ => (x.toNat : ℚ))
    (Tensor.Permutation.moduleMiddleHomology R N
      (ChainToCochain.cochain R P.complex) (ChainToCochain.cochain R Q.complex) n).toLinearEquiv.length_eq

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IteratedTorEuler
