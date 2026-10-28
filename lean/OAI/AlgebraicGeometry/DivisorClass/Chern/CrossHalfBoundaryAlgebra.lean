import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CrossBoundary

/-! # Cross Half Boundary Algebra -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CrossHalfBoundaryAlgebra

noncomputable section

/-!
# ChernClass: the signed boundary calculation for a half-disk product

The two terms are the outer-arc product with a tangent filling and the
half-disk product with its tangent boundary. Their common outer-arc
terms cancel. Only the axis-product boundary remains, with the
specified half-plane sign.
-/

open _root_.CategoryTheory OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k]

theorem singularCrossChain_smul_left (X Y : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (a : k) (x : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X p) (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X q) :
    Singular.CrossBoundary.singularCrossChain k X Y p q n h (a • x) y = a • Singular.CrossBoundary.singularCrossChain k X Y p q n h x y := by
  simp only [Singular.CrossBoundary.singularCrossChain, ← TensorProduct.smul_tmul', map_smul]

theorem singularCrossChain_halfDisk_boundary (X Y : TopCat.{0}) (q : ℕ) (a : k)
    (D : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X 2) (O I : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X 1)
    (B : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X (q + 2)) (z : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X (q + 1))
    (hD : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).d 2 1 D = O - a • I)
    (hO : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).d 1 0 O = a • ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).d 1 0 I)
    (hB : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).d (q + 2) (q + 1) B = z)
    (hz : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).d (q + 1) q z = 0) :
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y))).d (q + 3) (q + 2)
        (Singular.CrossBoundary.singularCrossChain k X Y 1 (q + 2) (q + 3) (by omega) O B +
          Singular.CrossBoundary.singularCrossChain k X Y 2 (q + 1) (q + 3) (by omega) D z) =
      a • ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y))).d (q + 3) (q + 2)
        (Singular.CrossBoundary.singularCrossChain k X Y 1 (q + 2) (q + 3) (by omega) I B) := by
  rw [map_add, Singular.CrossBoundary.singularCrossChain_boundary_interval_at k X Y (q + 1) (q + 3) (q + 2) (by omega) (by omega),
    Singular.CrossBoundary.singularCrossChain_boundary_disk_at k X Y q (q + 3) (q + 2) (by omega) (by omega),
    Singular.CrossBoundary.singularCrossChain_boundary_interval_at k X Y (q + 1) (q + 3) (q + 2) (by omega) (by omega), hD, hO, hB, hz]
  rw [singularCrossChain_smul_left, Singular.CrossBoundary.singularCrossChain_sub_left,
    singularCrossChain_smul_left, Singular.CrossBoundary.singularCrossChain_zero_right, add_zero, smul_sub]
  abel

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CrossHalfBoundaryAlgebra
