import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LeftBoundEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.EulerTransport

/-! # Euler Cutoff -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.EulerCutoff

noncomputable section

/-! Native Tor Euler sums stabilize at either input's genuine
projective-dimension bound. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LeftBoundEuler OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.EulerTransport.Tor

universe u
variable (R : Type u) [CommRing R] (M N : ModuleCat.{u} R)

theorem stable_left (d D : ℕ) [HasProjectiveDimensionLE M d] (hD : d ≤ D) :
    Euler.Tor.euler R M N D = Euler.Tor.euler R M N d := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hD 1))
  intro n _ hn
  have hdn : d < n := by simp only [Finset.mem_range] at hn; omega
  let := ModuleCat.subsingleton_of_isZero (LeftBoundEuler.tor_isZero_left R M N d n hdn)
  simp only [ExactLength.rationalLength, Module.length_eq_zero,
    ENat.toNat_zero, Nat.cast_zero, mul_zero]

theorem stable_right (d D : ℕ) [HasProjectiveDimensionLE N d] (hD : d ≤ D) :
    Euler.Tor.euler R M N D = Euler.Tor.euler R M N d :=
  (EulerTransport.Tor.comm R M N D).trans ((stable_left R N M d D hD).trans (EulerTransport.Tor.comm R N M d))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.EulerCutoff
