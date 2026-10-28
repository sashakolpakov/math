import OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteGroups

/-! # Group Diagram -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GroupDiagram.Construction

noncomputable section

/-! Designated commutative group objects in a finite diagram retain their
structures and chosen generic-fiber identifications. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.NumberField

universe u v w z

theorem finite_group_structures_on_models
    {K : Type u} [Field K] {s : Finset K} {I : Type v} {β : Type w} [Finite β]
    (M : I → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    (hM : ∀ i, Smooth (M i).hom ∧ IsProper (M i).hom)
    (X : I → Over (Spec (.of K)))
    (e : ∀ i, (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj (M i) ≅ X i)
    (index : β → I) (group : ∀ b, GrpObj (X (index b)))
    (hcomm : ∀ b, letI := group b; IsCommMonObj (X (index b))) :
    ∃ (t : Finset K) (h : s ⊆ t),
      let F := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
      let G := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)
      ∃ groupN : ∀ b, GrpObj (F.obj (M (index b))),
        ∀ b,
          (letI := groupN b; IsCommMonObj (F.obj (M (index b)))) ∧
          (letI := group b
           letI := groupN b
           letI : GrpObj (G.obj (F.obj (M (index b)))) := Functor.grpObjObj (F := G)
           IsMonHom ((GenericMorphisms.Construction.coefficientGenericComparisonAt h (M (index b)) ≪≫ e (index b)).hom)) := by
  let H := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
  let A := fun b ↦ M (index b)
  have (b : β) : Smooth (A b).hom := (hM (index b)).1
  have (b : β) : IsProper (A b).hom := (hM (index b)).2
  let groupA (b : β) : GrpObj (H.obj (A b)) := by
    let := group b
    exact GrpObj.ofIso (e (index b)).symm
  have (b : β) : IsCommMonObj (H.obj (A b)) := by
    let := group b
    have := hcomm b
    exact GroupReflection.Construction.commutative_group_of_iso (e (index b)).symm
  obtain ⟨t, h, groupN, hgN⟩ := FiniteGroups.Construction.finite_commutative_group_models_after_enlargement A
  let F := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
  let G := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)
  let c := GenericMorphisms.Construction.coefficientGenericComparison h
  refine ⟨t, h, groupN, fun b ↦ ⟨(hgN b).1, ?_⟩⟩
  let := group b
  let := groupN b
  let : GrpObj (G.obj (F.obj (A b))) := Functor.grpObjObj (F := G)
  let ec : G.obj (F.obj (A b)) ≅ H.obj (A b) := GenericMorphisms.Construction.coefficientGenericComparisonAt h (A b)
  have hc : IsMonHom ec.hom :=
    GroupReflection.Construction.image_group_iso_isMonHom G (F.obj (A b)) (H.obj (A b)) ec (groupN b) (hgN b).2
  have he : IsMonHom (e (index b)).hom := GroupReflection.Construction.transported_group_iso_isMonHom (e (index b))
  exact inferInstanceAs (IsMonHom (ec.hom ≫ (e (index b)).hom))

theorem finite_smooth_proper_group_diagram_coefficient_model
    {K : Type u} [Field K] [NumberField K]
    {I : Type v} {α : Type w} {β : Type z} [Finite I] [Finite α] [Finite β]
    (X : I → Over (Base.Construction.fieldBase K)) (hs : ∀ i, Smooth (X i).hom)
    (hp : ∀ i, IsProper (X i).hom) (src dst : α → I)
    (f : ∀ a, X (src a) ⟶ X (dst a))
    (index : β → I) (group : ∀ b, GrpObj (X (index b)))
    (hcomm : ∀ b, letI := group b; IsCommMonObj (X (index b))) :
    ∃ (s : Finset K) (M : I → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
      (fM : ∀ a, M (src a) ⟶ M (dst a))
      (e : ∀ i, (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj (M i) ≅ X i)
      (groupM : ∀ b, GrpObj (M (index b))),
      (∀ i, Smooth (M i).hom ∧ IsProper (M i).hom) ∧
      (∀ a, (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).map (fM a) ≫ (e (dst a)).hom =
        (e (src a)).hom ≫ f a) ∧
      (∀ b,
        letI := group b
        letI := groupM b
        letI : GrpObj ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj (M (index b))) :=
          Functor.grpObjObj
        IsCommMonObj (M (index b)) ∧ IsMonHom (e (index b)).hom) := by
  obtain ⟨s, M, p, fM, hM, hcart, hfM⟩ :=
    SpreadingOut.Finite.Construction.finite_smooth_proper_arrows_coefficient_model X hs hp src dst f
  let H := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
  let e (i : I) : H.obj (M i) ≅ X i :=
    Over.isoMk (hcart i).isoPullback.symm (hcart i).isoPullback_inv_snd
  have he (a : α) : H.map (fM a) ≫ (e (dst a)).hom = (e (src a)).hom ≫ f a :=
    Diagram.Construction.cartesian_generic_iso_compatibility _ _ _ (hcart _) (hcart _) (f a) (fM a) (hfM a)
  obtain ⟨t, h, groupN, hgroupN⟩ := finite_group_structures_on_models M hM X e index group hcomm
  let F := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
  let G := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)
  let c := GenericMorphisms.Construction.coefficientGenericComparison h
  refine ⟨t, (fun i ↦ F.obj (M i)), (fun a ↦ F.map (fM a)),
    (fun i ↦ GenericMorphisms.Construction.coefficientGenericComparisonAt h (M i) ≪≫ e i), groupN, ?_, ?_, ?_⟩
  · intro i
    have := (hM i).1
    have := (hM i).2
    exact ⟨inferInstanceAs (Smooth (pullback.snd (M i).hom _)),
      inferInstanceAs (IsProper (pullback.snd (M i).hom _))⟩
  · intro a
    have hc : G.map (F.map (fM a)) ≫ (c.app (M (dst a))).hom =
        (c.app (M (src a))).hom ≫ H.map (fM a) := c.hom.naturality (fM a)
    change G.map (F.map (fM a)) ≫ (c.app (M (dst a))).hom ≫ (e (dst a)).hom =
      ((c.app (M (src a))).hom ≫ (e (src a)).hom) ≫ f a
    rw [← Category.assoc, hc, Category.assoc, he, Category.assoc]
  · intro b
    exact hgroupN b

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GroupDiagram.Construction
