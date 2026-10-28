import OAI.ArithmeticGeometry.Models.SpreadingOut.SplitGroupDiagram
import Mathlib.CategoryTheory.Monoidal.CommMon_

/-! # Split Diagram -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SplitDiagram.Construction

noncomputable section

/-! Smooth proper arithmetic models of finite diagrams with designated
commutative group objects, preserving the chosen generic group isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.NumberField

universe u v w z

theorem finite_split_group_diagram_arithmetic_model
    {K : Type u} [Field K] [NumberField K]
    {I : Type v} {α : Type w} {β : Type z} [Finite I] [Finite α] [Finite β]
    (X : I → Over (Base.Construction.fieldBase K)) (hs : ∀ i, Smooth (X i).hom)
    (hp : ∀ i, IsProper (X i).hom) (hX : ∀ i, Base.Construction.HasSplitGeometricComponents (X i))
    (src dst : α → I)
    (f : ∀ a, X (src a) ⟶ X (dst a))
    (index : β → I) (group : ∀ b, GrpObj (X (index b)))
    (hcomm : ∀ b, letI := group b; IsCommMonObj (X (index b)))
    (hconn : ∀ b, GeometricallyConnected (X (index b)).hom) :
    ∃ (B : Base.Construction.ArithmeticOpen K) (M : I → Over B.U.toScheme)
      (fM : ∀ a, M (src a) ⟶ M (dst a))
      (e : ∀ i, (Over.pullback B.generic).obj (M i) ≅ X i)
      (groupM : ∀ b, GrpObj (M (index b))),
      (∀ i, Smooth (M i).hom ∧ IsProper (M i).hom ∧ Base.Construction.HasSplitGeometricComponents (M i)) ∧
      (∀ a, (Over.pullback B.generic).map (fM a) ≫ (e (dst a)).hom =
        (e (src a)).hom ≫ f a) ∧
      (∀ b,
        letI := group b
        letI := groupM b
        letI : GrpObj ((Over.pullback B.generic).obj (M (index b))) := Functor.grpObjObj
        IsCommMonObj (M (index b)) ∧ GeometricallyConnected (M (index b)).hom ∧
          IsMonHom (e (index b)).hom) := by
  obtain ⟨s, M, fM, e, groupM, hM, he, hgroup⟩ :=
    SplitGroupDiagram.Construction.finite_split_group_diagram_coefficient_model X hs hp hX src dst f index group hcomm hconn
  obtain ⟨B, b, hb⟩ := Diagram.Construction.coefficient_arithmetic_base s
  let F := Over.pullback b
  let G := Over.pullback B.generic
  let H := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
  let c : F ⋙ G ≅ H := Classical.choice ⟨
    (Over.pullbackComp B.generic b).symm ≪≫
      eqToIso (congrArg (fun k : Base.Construction.fieldBase K ⟶ CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s ↦ Over.pullback k) hb)⟩
  let ec (i : I) : G.obj (F.obj (M i)) ≅ H.obj (M i) := c.app (M i)
  let groupN (j : β) : GrpObj (F.obj (M (index j))) := by
    let := groupM j
    exact Functor.grpObjObj (F := F)
  refine ⟨B, (fun i ↦ F.obj (M i)), (fun a ↦ F.map (fM a)),
    (fun i ↦ ec i ≪≫ e i), groupN, ?_, ?_, ?_⟩
  · intro i
    have := (hM i).1
    have := (hM i).2.1
    exact ⟨inferInstanceAs (Smooth (pullback.snd (M i).hom b)),
      inferInstanceAs (IsProper (pullback.snd (M i).hom b)),
      SplitComponentsBaseChange.Construction.hasSplitGeometricComponents_baseChange b (M i) (hM i).2.2⟩
  · intro a
    have hc : G.map (F.map (fM a)) ≫ (ec (dst a)).hom =
        (ec (src a)).hom ≫ H.map (fM a) := c.hom.naturality (fM a)
    change G.map (F.map (fM a)) ≫ (ec (dst a)).hom ≫ (e (dst a)).hom =
      ((ec (src a)).hom ≫ (e (src a)).hom) ≫ f a
    rw [← Category.assoc, hc, Category.assoc, he, Category.assoc]
  · intro j
    let := group j
    let := groupM j
    let : GrpObj (F.obj (M (index j))) := groupN j
    let : GrpObj (G.obj (F.obj (M (index j)))) := Functor.grpObjObj (F := G)
    let : GrpObj (H.obj (M (index j))) := Functor.grpObjObj (F := H)
    have : IsCommMonObj (M (index j)) := (hgroup j).1
    have : GeometricallyConnected (M (index j)).hom := (hgroup j).2.1
    refine ⟨inferInstanceAs (IsCommMonObj (F.obj (M (index j)))),
      inferInstanceAs (GeometricallyConnected (pullback.snd (M (index j)).hom b)), ?_⟩
    have hc : IsMonHom (ec (index j)).hom := GroupBaseChange.Construction.baseChange_comparison_group_hom F G H c (M (index j))
    have he' : IsMonHom (e (index j)).hom := (hgroup j).2.2
    exact inferInstanceAs (IsMonHom ((ec (index j)).hom ≫ (e (index j)).hom))

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SplitDiagram.Construction
