import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits

/-! # Zero Differential -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.ZeroDifferential.CechZeroDifferential

noncomputable section

/-!
# The first differential of the actual Čech cochain complex

The first differential is the difference of the two coface restrictions.
Its individual components are expressed through the original nerve maps,
so a zero-cocycle supplies the compatibility equations used in gluing.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe w v u v' u'

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A] [Preadditive A]
  (E : SimplicialObject (FormalCoproduct.{w} C)) (P : Cᵒᵖ ⥤ A)

theorem differential :
    ((FormalCoproduct.cochainComplexFunctor E).obj P).d 0 1 =
      ((FormalCoproduct.cosimplicialObjectFunctor E).obj P).map (SimplexCategory.δ (0 : Fin 2)) -
        ((FormalCoproduct.cosimplicialObjectFunctor E).obj P).map (SimplexCategory.δ (1 : Fin 2)) := by
  let Y := (FormalCoproduct.cosimplicialObjectFunctor E).obj P
  have hd : ((FormalCoproduct.cochainComplexFunctor E).obj P).d 0 1 =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD Y 0 :=
    CochainComplex.of_d (fun n => Y.obj ⦋n⦌)
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD Y) 0
  have hs := Fin.sum_univ_two (fun i : Fin 2 => (-1 : ℤ) ^ (i : ℕ) •
    Y.map (SimplexCategory.δ i))
  exact hd.trans (hs.trans (by
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, sub_eq_add_neg]
    rfl))

def face (i : Fin 2) : E.obj (op ⦋1⦌) ⟶ E.obj (op ⦋0⦌) := E.map (SimplexCategory.δ i).op

theorem differential_component (t : (E.obj (op ⦋1⦌)).I) :
    ((FormalCoproduct.cochainComplexFunctor E).obj P).d 0 1 ≫
      Pi.π (fun i => P.obj (op ((E.obj (op ⦋1⦌)).obj i))) t =
        (Pi.π (fun i => P.obj (op ((E.obj (op ⦋0⦌)).obj i))) ((face E 0).f t) ≫
          P.map ((face E 0).φ t).op) -
        (Pi.π (fun i => P.obj (op ((E.obj (op ⦋0⦌)).obj i))) ((face E 1).f t) ≫
          P.map ((face E 1).φ t).op) := by
  rw [differential]
  change ((Pi.lift (fun i => Pi.π (fun j => P.obj (op ((E.obj (op ⦋0⦌)).obj j)))
    ((face E 0).f i) ≫ P.map ((face E 0).φ i).op)) -
    (Pi.lift (fun i => Pi.π (fun j => P.obj (op ((E.obj (op ⦋0⦌)).obj j)))
      ((face E 1).f i) ≫ P.map ((face E 1).φ i).op))) ≫ Pi.π _ t = _
  simp only [Preadditive.sub_comp, Pi.lift_comp_π]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.ZeroDifferential.CechZeroDifferential
