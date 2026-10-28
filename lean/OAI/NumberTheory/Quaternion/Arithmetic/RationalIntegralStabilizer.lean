import OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicLattice
import OAI.NumberTheory.Quaternion.Arithmetic.LocalAdeles
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices

/-! # Rational Integral Stabilizer -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.RationalIntegralStabilizer

noncomputable section

/-! Rational matrices integral at all finite places preserve the
standard ring-of-integers lattice. -/

open scoped Classical _root_.NumberField
open OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices.Construction IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem rational_integralAtAll_mem_standard_stabilizer (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (q : G.RationalPoints)
    (hq : ∀ v : HeightOneSpectrum (𝓞 F), LocalAdeles.diagonalLocal G (.inr v) q ∈ LocalAdeles.integralLocalSubgroup G (.inr v)) :
    q ∈ G.latticeStabilizer (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n) := by
  apply (ArithmeticGroups.Lattices.Integral.Matrices.Construction.standard_lattice_stabilizer_iff_integral G q).mpr
  apply ArithmeticGroups.Lattices.Integral.Matrices.Construction.specialLinear_lift_of_integral_entries q.val
  intro i j
  apply (FiniteAdelicLattice.scalarFiniteAdele_integral_iff (q.val i j)).mp
  intro v
  exact (hq v).1 i j

end

end OAI.NumberTheory.Quaternion.Arithmetic.RationalIntegralStabilizer
