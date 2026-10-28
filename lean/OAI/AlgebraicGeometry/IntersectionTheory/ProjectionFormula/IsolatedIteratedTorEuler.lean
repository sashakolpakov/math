import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IteratedTorEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.FiniteLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Euler

/-! # Isolated Iterated Tor Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedIteratedTorEuler

noncomputable section

/-! At an isolated triple intersection of finite modules, all iterated
Tor lengths are finite. Projective-dimension bounds then give the native
iterated Euler identity without separate finiteness assumptions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsNoetherianRing R]
  (L M N : ModuleCat.{0} R) [Module.Finite R L] [Module.Finite R M] [Module.Finite R N]

theorem length_ne_top (p : PrimeSpectrum R)
    (h : (Module.support R N ∩ Module.support R M) ∩ Module.support R L ⊆ {p}) (i j : ℕ) :
    Module.length R (((Tor (ModuleCat.{0} R) i).obj (((Tor (ModuleCat.{0} R) j).obj N).obj M)).obj L) ≠ ⊤ := by
  let := ProjectionFormula.Finite.Tor.finite R N M j
  apply ProjectionFormula.Tor.FiniteLength.tor_length_ne_top R _ L p _ i
  exact (Set.inter_subset_inter_left _ (ProjectionFormula.Tor.Support.support_subset R N M j)).trans h

theorem commute (a b : ℕ) [HasProjectiveDimensionLE L a] [HasProjectiveDimensionLE M b]
    (p : PrimeSpectrum R)
    (h : (Module.support R N ∩ Module.support R M) ∩ Module.support R L ⊆ {p}) :
    IteratedTorEuler.euler R L M N a b = IteratedTorEuler.euler R M L N b a := by
  obtain ⟨P, hP⟩ := BoundedResolution.exists_bounded_resolution R M b
  obtain ⟨Q, hQ⟩ := BoundedResolution.exists_bounded_resolution R L a
  have h' : (Module.support R N ∩ Module.support R L) ∩ Module.support R M ⊆ {p} := by
    intro q hq
    exact h ⟨⟨hq.1.1, hq.2⟩, hq.1.2⟩
  exact IteratedTorEuler.commute R L M N P Q a b hP hQ
    (fun i _ j _ => length_ne_top R L M N p h i j)
    (fun j _ i _ => length_ne_top R M L N p h' j i)

omit [IsNoetherianRing R] [Module.Finite R L] [Module.Finite R M] [Module.Finite R N] in
theorem euler_eq_sum (a b : ℕ) :
    IteratedTorEuler.euler R L M N a b =
      ∑ j ∈ Finset.range (b + 1), (-1 : ℚ) ^ j *
        ProjectionFormula.Tor.Euler.euler R (((Tor (ModuleCat.{0} R) j).obj N).obj M) L a := by
  unfold IteratedTorEuler.euler ProjectionFormula.Tor.Euler.euler
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]
  ring

theorem alternating_euler (a b : ℕ) [HasProjectiveDimensionLE L a] [HasProjectiveDimensionLE M b]
    (p : PrimeSpectrum R)
    (h : (Module.support R N ∩ Module.support R M) ∩ Module.support R L ⊆ {p}) :
    (∑ j ∈ Finset.range (b + 1), (-1 : ℚ) ^ j *
      ProjectionFormula.Tor.Euler.euler R (((Tor (ModuleCat.{0} R) j).obj N).obj M) L a) =
    ∑ i ∈ Finset.range (a + 1), (-1 : ℚ) ^ i *
      ProjectionFormula.Tor.Euler.euler R (((Tor (ModuleCat.{0} R) i).obj N).obj L) M b := by
  rw [← euler_eq_sum, ← euler_eq_sum]
  exact commute R L M N a b p h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedIteratedTorEuler
