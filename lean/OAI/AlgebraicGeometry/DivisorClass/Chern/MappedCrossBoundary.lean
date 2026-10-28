import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CrossBoundary

/-! # Mapped Cross Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.MappedCrossBoundary

noncomputable section

/-! The native cross-product boundary equations after an actual continuous map. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k]

theorem mappedCross_boundary_point (X Y Z : TopCat.{0}) (f : TopCat.of (X × Y) ⟶ Z) (q : ℕ)
    (x : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X 0) (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X (q + 1)) :
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Z).d (q + 1) q
      (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f).f (q + 1) (Singular.CrossBoundary.singularCrossChain k X Y 0 (q + 1) (q + 1) (by omega) x y)) =
      ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f).f q (Singular.CrossBoundary.singularCrossChain k X Y 0 q q (by omega) x
        (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).d (q + 1) q y)) := by
  have h := ConcreteCategory.congr_hom (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f).comm (q + 1) q)
    (Singular.CrossBoundary.singularCrossChain k X Y 0 (q + 1) (q + 1) (by omega) x y)
  change _ = ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f).f q
    (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y))).d (q + 1) q _) at h
  rw [Singular.CrossBoundary.singularCrossChain_boundary_point] at h
  exact h

theorem mappedCross_boundary_interval (X Y Z : TopCat.{0}) (f : TopCat.of (X × Y) ⟶ Z)
    (q n m : ℕ) (hn : 1 + (q + 1) = n) (hm : 0 + (q + 1) = m)
    (x : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X 1) (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X (q + 1)) :
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Z).d n m
      (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f).f n (Singular.CrossBoundary.singularCrossChain k X Y 1 (q + 1) n hn x y)) =
      ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f).f m
        (Singular.CrossBoundary.singularCrossChain k X Y 0 (q + 1) m hm (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).d 1 0 x) y -
          Singular.CrossBoundary.singularCrossChain k X Y 1 q m (by omega) x (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).d (q + 1) q y)) := by
  have h := ConcreteCategory.congr_hom (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f).comm n m)
    (Singular.CrossBoundary.singularCrossChain k X Y 1 (q + 1) n hn x y)
  change _ = ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f).f m (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y))).d n m _) at h
  rw [Singular.CrossBoundary.singularCrossChain_boundary_interval_at k X Y q n m hn hm] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.MappedCrossBoundary
