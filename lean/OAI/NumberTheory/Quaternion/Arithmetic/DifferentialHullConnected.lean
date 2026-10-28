import OAI.NumberTheory.Quaternion.Arithmetic.DifferentialPrime
import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullGroup
import OAI.NumberTheory.ArithmeticGroups.Lattices.ConnectedBaseChange

/-! # Differential Hull Connected -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.DifferentialHullConnected

noncomputable section

/-! The algebraic hull of infinitesimal directions is irreducible and
connected. Its vanishing ideal is the prime differential core. -/

open scoped Classical
open Set _root_.Topology

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

theorem matrixDifferentialCore_isPrime (S : Set (Matrix (Fin n) (Fin n) k)) :
    (ArithmeticGroups.Lattices.MatrixDifferential.Construction.matrixDifferentialCore S).IsPrime := by
  let : (RingHom.ker (ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) (1 : ArithmeticGroups.Lattices.Algebraic.SL n k))).IsPrime :=
    RingHom.ker_isPrime _
  exact DifferentialPrime.differentialCore_isPrime _ _

variable [IsAlgClosed k] (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n)

local instance differentialHullRationalTopology : TopologicalSpace G.RationalPoints := ArithmeticGroups.Lattices.RationalZariski.Construction.rationalZariskiTopology G

theorem differentialHull_irreducible
    (S : Set (Matrix (Fin n) (Fin n) k)) (hS : S ⊆ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    IrreducibleSpace (ArithmeticGroups.Lattices.DifferentialHullGroup.Construction.differentialHullSubgroup G S) := by
  let N := ArithmeticGroups.Lattices.DifferentialHullGroup.Construction.differentialHullSubgroup G S
  let f : N → PrimeSpectrum (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k) := fun g => ArithmeticGroups.Lattices.RationalZariski.Construction.rationalPrime G g.val
  have he : PrimeSpectrum.vanishingIdeal (range f) = ArithmeticGroups.Lattices.DifferentialHullGroup.Construction.hullVanishingIdeal G S := by
    ext p
    simp only [PrimeSpectrum.mem_vanishingIdeal, forall_mem_range, ArithmeticGroups.Lattices.DifferentialHullGroup.Construction.hullVanishingIdeal,
      Ideal.mem_iInf]
    rfl
  have hp : (PrimeSpectrum.vanishingIdeal (range f)).IsPrime := by
    rw [he, ArithmeticGroups.Lattices.DifferentialHullGroup.Construction.hullVanishingIdeal_eq_core G S hS]
    exact matrixDifferentialCore_isPrime S
  apply ArithmeticGroups.Lattices.ConnectedBaseChange.Construction.irreducible_of_inducing_range
    ((show IsInducing (ArithmeticGroups.Lattices.RationalZariski.Construction.rationalPrime G) from ⟨rfl⟩).comp IsInducing.subtypeVal)
  exact PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mpr hp

theorem differentialHull_connected
    (S : Set (Matrix (Fin n) (Fin n) k)) (hS : S ⊆ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    IsConnected (ArithmeticGroups.Lattices.DifferentialHullGroup.Construction.differentialHullSubgroup G S : Set G.RationalPoints) := by
  let : IrreducibleSpace (ArithmeticGroups.Lattices.DifferentialHullGroup.Construction.differentialHullSubgroup G S) := differentialHull_irreducible G S hS
  exact isConnected_iff_connectedSpace.mpr inferInstance

omit [CharZero k] [IsAlgClosed k] in
theorem differentialHull_closed (S : Set (Matrix (Fin n) (Fin n) k)) :
    IsClosed (ArithmeticGroups.Lattices.DifferentialHullGroup.Construction.differentialHullSubgroup G S : Set G.RationalPoints) :=
  ArithmeticGroups.Lattices.DifferentialHullGroup.Construction.differentialHullSubmonoid_closed G S

end

end OAI.NumberTheory.Quaternion.Arithmetic.DifferentialHullConnected
