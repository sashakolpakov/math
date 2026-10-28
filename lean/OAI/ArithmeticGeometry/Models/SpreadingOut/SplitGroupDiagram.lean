import OAI.ArithmeticGeometry.Models.SpreadingOut.SplitFinite
import OAI.ArithmeticGeometry.Models.SpreadingOut.GroupDiagram

/-! # Split Group Diagram -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SplitGroupDiagram.Construction

noncomputable section

/-! Split geometric components and connected designated group models
survive simultaneous descent of the group structures and arrows. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.NumberField

universe u v w z

theorem finite_split_group_diagram_coefficient_model
    {K : Type u} [Field K] [NumberField K]
    {I : Type v} {α : Type w} {β : Type z} [Finite I] [Finite α] [Finite β]
    (X : I → Over (Base.Construction.fieldBase K)) (hs : ∀ i, Smooth (X i).hom)
    (hp : ∀ i, IsProper (X i).hom) (hX : ∀ i, Base.Construction.HasSplitGeometricComponents (X i))
    (src dst : α → I)
    (f : ∀ a, X (src a) ⟶ X (dst a))
    (index : β → I) (group : ∀ b, GrpObj (X (index b)))
    (hcomm : ∀ b, letI := group b; IsCommMonObj (X (index b)))
    (hconn : ∀ b, GeometricallyConnected (X (index b)).hom) :
    ∃ (s : Finset K) (M : I → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
      (fM : ∀ a, M (src a) ⟶ M (dst a))
      (e : ∀ i, (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj (M i) ≅ X i)
      (groupM : ∀ b, GrpObj (M (index b))),
      (∀ i, Smooth (M i).hom ∧ IsProper (M i).hom ∧ Base.Construction.HasSplitGeometricComponents (M i)) ∧
      (∀ a, (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).map (fM a) ≫ (e (dst a)).hom =
        (e (src a)).hom ≫ f a) ∧
      (∀ b,
        letI := group b
        letI := groupM b
        letI : GrpObj ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj (M (index b))) :=
          Functor.grpObjObj
        IsCommMonObj (M (index b)) ∧ GeometricallyConnected (M (index b)).hom ∧
          IsMonHom (e (index b)).hom) := by
  obtain ⟨s, M, p, fM, hM, hcart, hfM, hconnM⟩ :=
    SplitFinite.Construction.finite_split_arrows_coefficient_model X hs hp hX src dst f
  let H := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
  let e (i : I) : H.obj (M i) ≅ X i :=
    Over.isoMk (hcart i).isoPullback.symm (hcart i).isoPullback_inv_snd
  have he (a : α) : H.map (fM a) ≫ (e (dst a)).hom = (e (src a)).hom ≫ f a :=
    Diagram.Construction.cartesian_generic_iso_compatibility _ _ _ (hcart _) (hcart _) (f a) (fM a) (hfM a)
  obtain ⟨t, h, groupN, hgroupN⟩ := GroupDiagram.Construction.finite_group_structures_on_models M (fun i ↦ ⟨(hM i).1, (hM i).2.1⟩)
      X e index group hcomm
  let F := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
  let G := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)
  let c := GenericMorphisms.Construction.coefficientGenericComparison h
  refine ⟨t, (fun i ↦ F.obj (M i)), (fun a ↦ F.map (fM a)),
    (fun i ↦ GenericMorphisms.Construction.coefficientGenericComparisonAt h (M i) ≪≫ e i), groupN, ?_, ?_, ?_⟩
  · intro i
    have := (hM i).1
    have := (hM i).2.1
    exact ⟨inferInstanceAs (Smooth (pullback.snd (M i).hom _)),
      inferInstanceAs (IsProper (pullback.snd (M i).hom _)),
      SplitComponentsBaseChange.Construction.hasSplitGeometricComponents_baseChange _ (M i) (hM i).2.2⟩
  · intro a
    have hc : G.map (F.map (fM a)) ≫ (c.app (M (dst a))).hom =
        (c.app (M (src a))).hom ≫ H.map (fM a) := c.hom.naturality (fM a)
    change G.map (F.map (fM a)) ≫ (c.app (M (dst a))).hom ≫ (e (dst a)).hom =
      ((c.app (M (src a))).hom ≫ (e (src a)).hom) ≫ f a
    rw [← Category.assoc, hc, Category.assoc, he, Category.assoc]
  · intro b
    have := hconnM (index b) (hconn b)
    exact ⟨(hgroupN b).1,
      inferInstanceAs (GeometricallyConnected (pullback.snd (M (index b)).hom _)),
      (hgroupN b).2⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SplitGroupDiagram.Construction
