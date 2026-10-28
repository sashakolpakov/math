import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.Extension
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MonoidalHomReflection
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison

/-! # Group Rigidity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.GroupRigidity

noncomputable section

/-! Pointed group rigidity and uniqueness of the dual group law hold over an arbitrary field by faithful algebraic-closure base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

/-- Group compatibility can be checked after the faithfully flat extension to an algebraic closure. -/
theorem pointed_isMonHom {k : Type u} [Field k]
    (A B : Over (Spec (.of k))) [groupA : GrpObj A] [commA : IsCommMonObj A] [groupB : GrpObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [LocallyOfFiniteType B.hom] [IsSeparated B.hom]
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let F := Over.pullback s
  have : F.Faithful := Extension.pullback_faithful s
  have : Smooth (F.obj A).hom := inferInstanceAs (Smooth (pullback.snd A.hom s))
  have : IsProper (F.obj A).hom := inferInstanceAs (IsProper (pullback.snd A.hom s))
  have : GeometricallyConnected (F.obj A).hom := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom s))
  have : LocallyOfFiniteType (F.obj B).hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd B.hom s))
  have : IsSeparated (F.obj B).hom := inferInstanceAs (IsSeparated (pullback.snd B.hom s))
  have hs : η[F.obj A] ≫ F.map f = η[F.obj B] := by
    change (Functor.LaxMonoidal.ε F ≫ F.map η[A]) ≫ F.map f = Functor.LaxMonoidal.ε F ≫ F.map η[B]
    exact (Category.assoc _ _ _).trans
      (congrArg (fun t => Functor.LaxMonoidal.ε F ≫ t)
        ((F.map_comp η[A] f).symm.trans (congrArg F.map hf)))
  have : IsMonHom (F.map f) := Homomorphisms.GroupRigidity.Construction.pointed_isMonHom (F.obj A) (F.obj B) (F.map f) hs
  exact MonoidalHomReflection.isMonHom F f

/-- The origin determines the group structure on a smooth proper geometrically connected field scheme. -/
theorem groupStructure_eq_of_origin {k : Type u} [Field k]
    (X : Over (Spec (.of k))) (G H : GrpObj X) (hcomm : letI := G; IsCommMonObj X)
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (hunit : G.toMonObj.one = H.toMonObj.one) : G = H := by
  have h := pointed_isMonHom (groupA := G) (commA := hcomm) (groupB := H) X X (𝟙 X)
    ((Category.comp_id G.toMonObj.one).trans hunit)
  have hm := @IsMonHom.mul_hom _ _ _ _ _ G.toMonObj H.toMonObj (𝟙 X) h
  have hmul : G.toMonObj.mul = H.toMonObj.mul := by
    simpa only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp] using hm
  exact GrpObj.ext G H (Homomorphisms.DualGroupComparison.Construction.monObj_eq_of_operations G.toMonObj H.toMonObj hunit hmul)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.GroupRigidity
