import OAI.AlgebraicGeometry.GroupSchemes.AffineHopf
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra

/-! # Cartier -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-!
# FiniteEtale: finite Cartier duals of the given geometric group schemes

The dual's Hopf algebra is the convolution dual of the coordinate Hopf algebra
recovered from the input scheme. The dual algebra construction and its Hopf
axioms are proved in DualAlgebra; no statement placeholder is imported.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra.Construction

universe u

variable {k : Type u} [Field k]

/-- A finite cocommutative Hopf algebra gives an actual commutative group scheme. -/
def FiniteEtale.FiniteCommGroupScheme.ofHopf (A : Type u) [CommRing A] [HopfAlgebra k A]
    [Coalgebra.IsCocomm k A] [Module.Finite k A] : FiniteEtale.FiniteCommGroupScheme k where
  algebra := CommAlgCat.of k A
  finite := inferInstance
  group := by
    change CommGrpObj ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k)))
    exact AlgebraicGeometry.instCommGrpObjSpecAsOverSpec
      (R := CommRingCat.of k) (A := CommRingCat.of A)

/-- The finite dual group scheme, for a coordinate algebra with fixed instances. -/
def FiniteEtale.FiniteCommGroupScheme.dualOfHopf (A : Type u) [CommRing A] [HopfAlgebra k A]
    [Coalgebra.IsCocomm k A] [Module.Finite k A] : FiniteEtale.FiniteCommGroupScheme k :=
  FiniteEtale.FiniteCommGroupScheme.ofHopf (k := k) (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A)

theorem FiniteEtale.FiniteCommGroupScheme.dualOfHopf_rank (A : Type u) [CommRing A] [HopfAlgebra k A]
    [Coalgebra.IsCocomm k A] [Module.Finite k A] :
    Module.finrank k (FiniteEtale.FiniteCommGroupScheme.dualOfHopf (k := k) A).algebra = Module.finrank k A := by
  change Module.finrank k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) = _
  rw [(AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateLinearEquiv k A).finrank_eq]
  exact Subspace.dual_finrank_eq

/-- Cartier duality on finite commutative group schemes over k. -/
def FiniteEtale.FiniteCommGroupScheme.cartierDual (G : FiniteEtale.FiniteCommGroupScheme k) : FiniteEtale.FiniteCommGroupScheme k := by
  exact @FiniteEtale.FiniteCommGroupScheme.dualOfHopf k _ G.algebra _ G.coordinateHopf G.coordinateHopf_cocomm G.finite

/-- The coordinate dimension, and hence the order, is preserved by Cartier duality. -/
theorem FiniteEtale.FiniteCommGroupScheme.cartierDual_rank (G : FiniteEtale.FiniteCommGroupScheme k) :
    Module.finrank k G.cartierDual.algebra = Module.finrank k G.algebra := by
  exact @FiniteEtale.FiniteCommGroupScheme.dualOfHopf_rank k _ G.algebra _ G.coordinateHopf G.coordinateHopf_cocomm G.finite

end

end OAI.AlgebraicGeometry.GroupSchemes
