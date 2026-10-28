import OAI.NumberTheory.ArithmeticGroups.Lattices.RationalZariski
import OAI.NumberTheory.ArithmeticGroups.Lattices.BaseChange

/-! # Geometric Point Topology -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.GeometricPointTopology

noncomputable section

/-! The rational points of the geometric base change and the original
geometric points agree as topological groups with their specified
Zariski topologies. -/

open _root_.Topology

variable {k : Type} [Field k] {n : ℕ}

def geometricBaseChangePointEquiv (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k))).RationalPoints ≃*
      G.GeometricPoints :=
  MulEquiv.subgroupCongr (by
    change G.subgroup (AlgebraicClosure k)
      ((RingHom.id (AlgebraicClosure k)).comp (algebraMap k (AlgebraicClosure k))) = _
    rw [RingHom.id_comp])

def geometricBaseChangePointHomeomorph (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    @Homeomorph (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k))).RationalPoints
      G.GeometricPoints
      (ArithmeticGroups.Lattices.RationalZariski.Construction.rationalZariskiTopology (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k))))
      G.geometricTopology := by
  let H := ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k))
  let : TopologicalSpace H.RationalPoints := ArithmeticGroups.Lattices.RationalZariski.Construction.rationalZariskiTopology H
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  let e := geometricBaseChangePointEquiv G
  refine { e.toEquiv with continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply continuous_induced_rng.mpr
    change Continuous (G.geometricPrime ∘ e)
    have hp : G.geometricPrime ∘ e = ArithmeticGroups.Lattices.RationalZariski.Construction.rationalPrime H := by
      funext y
      apply PrimeSpectrum.ext
      rfl
    rw [hp]
    exact continuous_induced_dom
  · apply continuous_induced_rng.mpr
    change Continuous (ArithmeticGroups.Lattices.RationalZariski.Construction.rationalPrime H ∘ e.symm)
    have hp : ArithmeticGroups.Lattices.RationalZariski.Construction.rationalPrime H ∘ e.symm = G.geometricPrime := by
      funext y
      apply PrimeSpectrum.ext
      rfl
    rw [hp]
    exact continuous_induced_dom

end

end OAI.NumberTheory.Quaternion.Arithmetic.GeometricPointTopology
