import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitCosetComponents
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CosetNeighbors

/-! # Lattice Coset Convolution -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeCosetConvolution

noncomputable section

/-! The actual raw convolution law transfers through the proved split
coset/lattice equivalence, retaining every terminal multiplicity. -/

section Multisets
variable {X Y : Type*}

def multisetMapHom (f : X → Y) : Multiset X →+ Multiset Y where
  toFun := Multiset.map f
  map_zero' := rfl
  map_add' := Multiset.map_add f

def transportNeighbors (e : X ≃ Y) (N : X → Multiset X) (y : Y) : Multiset Y :=
  (N (e.symm y)).map e

theorem transportNeighbors_bind (e : X ≃ Y) (N M : X → Multiset X) (y : Y) :
    (transportNeighbors e N y).bind (transportNeighbors e M) =
      ((N (e.symm y)).bind M).map e := by
  simp only [transportNeighbors, Multiset.bind_map, Multiset.map_bind,
    Equiv.symm_apply_apply]

end Multisets

variable (s q : ℕ) [Fact q.Prime]

abbrev SplitLatticePoint :=
  (Fin s → Duality.RankThreeLattice ℤ_[q] ℚ_[q]) × (ℚ_[q]ˣ ⧸ SplitCosetComponents.scalarIntegralLevel q)

def sphericalLatticeNeighbors (t : Local.LocalType s) : SplitLatticePoint s q → Multiset (SplitLatticePoint s q) :=
  transportNeighbors (SplitCosetComponents.splitCosetLatticeEquiv s q) (CosetNeighbors.sphericalCosetNeighbors s q t)

theorem sphericalLatticeNeighbors_convolution (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (u v : Local.IntegralType s) (x : SplitLatticePoint s q) :
    (sphericalLatticeNeighbors s q u.val x).bind (sphericalLatticeNeighbors s q v.val) =
      (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum (fun w n => n • sphericalLatticeNeighbors s q w.val x) := by
  rw [sphericalLatticeNeighbors, sphericalLatticeNeighbors, transportNeighbors_bind,
    CosetNeighbors.sphericalCosetNeighbors_convolution s q hElementaryDivisors]
  exact (map_finsuppSum (multisetMapHom (SplitCosetComponents.splitCosetLatticeEquiv s q)) _ _).trans (by
    apply Finsupp.sum_congr
    intro w _
    exact map_nsmul (multisetMapHom (SplitCosetComponents.splitCosetLatticeEquiv s q)) _ _)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeCosetConvolution
