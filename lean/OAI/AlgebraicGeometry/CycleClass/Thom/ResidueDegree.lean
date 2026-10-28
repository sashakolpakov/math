import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.ResidueDegree
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Residue Degree -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ResidueDegree.Constructions

noncomputable section

/-! The actual residue-field degree obeys the tower law and is one for immersions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem residueDegree_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f x) * f.residueDegree x := by
  let K := Z.residueField (g (f x))
  let L := Y.residueField (f x)
  let M := X.residueField x
  let a : K →+* L := (g.residueFieldMap (f x)).hom
  let b : L →+* M := (f.residueFieldMap x).hom
  let : Algebra K L := a.toAlgebra
  let : Algebra L M := b.toAlgebra
  let : Algebra K M := ((f ≫ g).residueFieldMap x).hom.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f g x))
  exact (Module.finrank_mul_finrank K L M).symm

theorem residueDegree_immersion {A B : Scheme.{u}} (i : A ⟶ B)
    [SurjectiveOnStalks i] (x : A) : i.residueDegree x = 1 := by
  have h := ProperImage.ResidueDegree.Constructions.Construction.residueDegree_post_immersion (𝟙 A) i x
  simpa only [Category.id_comp, Scheme.Hom.residueDegree_id] using h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ResidueDegree.Constructions
