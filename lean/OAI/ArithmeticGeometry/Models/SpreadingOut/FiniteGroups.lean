import OAI.ArithmeticGeometry.Models.SpreadingOut.Group

/-! # Finite Groups -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteGroups.Construction

noncomputable section

/-! A finite family of generic commutative group structures descends to one
common coefficient stage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.CategoryTheory.Functor
open scoped _root_.NumberField

universe u v

theorem finite_group_operations_descend_raw
    {K : Type u} [Field K] {s : Finset K} {β : Type v} [Finite β]
    (M : β → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    [∀ b, Smooth (M b).hom] [∀ b, IsProper (M b).hom]
    [∀ b, GrpObj ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj (M b))] :
    ∃ (t : Finset K) (h : s ⊆ t),
      let F := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
      let G := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)
      let H := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
      let c := GenericMorphisms.Construction.coefficientGenericComparison h
      ∃ (a : ∀ b, F.obj (𝟙_ _) ⟶ F.obj (M b))
        (m : ∀ b, F.obj (M b ⊗ M b) ⟶ F.obj (M b))
        (d : ∀ b, F.obj (M b) ⟶ F.obj (M b)),
        ∀ b,
          (G.map (a b) ≫ (c.app (M b)).hom =
            (c.app (𝟙_ _)).hom ≫ OplaxMonoidal.η H ≫ η[H.obj (M b)]) ∧
          (G.map (m b) ≫ (c.app (M b)).hom =
            (c.app (M b ⊗ M b)).hom ≫ OplaxMonoidal.δ H (M b) (M b) ≫ μ[H.obj (M b)]) ∧
          (G.map (d b) ≫ (c.app (M b)).hom = (c.app (M b)).hom ≫ ι[H.obj (M b)]) := by
  let H := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
  let D : β × Fin 3 → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s) :=
    fun p ↦ GroupOperationDescent.Construction.groupOperationObjects (M p.1) p.2
  let src : β × Fin 3 → β × Fin 3 := fun p ↦ (p.1, GroupOperationDescent.Construction.groupOperationSources p.2)
  let dst : β × Fin 3 → β × Fin 3 := fun p ↦ (p.1, 1)
  let a : ∀ p, H.obj (D (src p)) ⟶ H.obj (D (dst p)) :=
    fun p ↦ GroupOperationDescent.Construction.groupOperationMaps H (M p.1) p.2
  obtain ⟨t, h, b, hb⟩ := GenericMorphisms.Construction.finite_generic_morphisms_descend D
    (fun p ↦ GroupOperationDescent.Construction.groupOperationObjects_finitePresentation (M p.1) p.2) src dst a
  exact ⟨t, h, (fun j ↦ b (j, 0)), (fun j ↦ b (j, 1)), (fun j ↦ b (j, 2)),
    fun j ↦ ⟨hb (j, 0), hb (j, 1), hb (j, 2)⟩⟩

theorem finite_commutative_group_models_after_enlargement
    {K : Type u} [Field K] {s : Finset K} {β : Type v} [Finite β]
    (M : β → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    [∀ b, Smooth (M b).hom] [∀ b, IsProper (M b).hom]
    [∀ b, GrpObj ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj (M b))]
    [∀ b, IsCommMonObj ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj (M b))] :
    ∃ (t : Finset K) (h : s ⊆ t),
      let F := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
      let G := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)
      ∃ groupN : ∀ b, GrpObj (F.obj (M b)),
        ∀ b, (letI := groupN b; IsCommMonObj (F.obj (M b))) ∧
          (letI := groupN b
           Functor.grpObjObj (F := G) (G := F.obj (M b)) =
             GrpObj.ofIso ((GenericMorphisms.Construction.coefficientGenericComparison h).app (M b)).symm) := by
  obtain ⟨t, h, a, m, d, hab⟩ := finite_group_operations_descend_raw M
  let F := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
  let G := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)
  let H := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
  let c := GenericMorphisms.Construction.coefficientGenericComparison h
  let N := fun b ↦ F.obj (M b)
  let genericGroup (b : β) : GrpObj (G.obj (N b)) := GrpObj.ofIso (c.app (M b)).symm
  have (b : β) : IsCommMonObj (G.obj (N b)) := GroupReflection.Construction.commutative_group_of_iso (c.app (M b)).symm
  have (b : β) : Smooth (N b).hom := inferInstanceAs (Smooth (pullback.snd (M b).hom _))
  have (b : β) : IsProper (N b).hom := inferInstanceAs (IsProper (pullback.snd (M b).hom _))
  have : Smooth (𝟙_ (Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K t))).hom := inferInstanceAs (Smooth (𝟙 _))
  have (b : β) : Smooth (N b ⊗ N b).hom := Group.Construction.smooth_over_tensor _ _
  have (b : β) : Smooth ((𝟙_ (Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K t))) ⊗ N b).hom :=
    Group.Construction.smooth_over_tensor _ _
  have (b : β) : Smooth (N b ⊗ (𝟙_ (Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K t)))).hom :=
    Group.Construction.smooth_over_tensor _ _
  have (b : β) : Smooth ((N b ⊗ N b) ⊗ N b).hom := Group.Construction.smooth_over_tensor _ _
  have hInject (b : β) (Y : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K t)) [Smooth Y.hom] :
      Function.Injective (G.map : (Y ⟶ N b) → _) :=
    GenericFaithfulness.Construction.generic_pullback_map_injective (algebraMap (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K t) K) Subtype.val_injective
  let one (b : β) := LaxMonoidal.ε F ≫ a b
  let mul (b : β) := LaxMonoidal.μ F (M b) (M b) ≫ m b
  have hOne (b : β) : G.map (one b) = OplaxMonoidal.η G ≫ η[G.obj (N b)] :=
    GroupBaseChange.Construction.descended_one_image F G H c (M b) (a b) (hab b).1
  have hMul (b : β) : G.map (mul b) = OplaxMonoidal.δ G (N b) (N b) ≫ μ[G.obj (N b)] :=
    GroupBaseChange.Construction.descended_mul_image F G H c (M b) (m b) (hab b).2.1
  have hInv (b : β) : G.map (d b) = ι[G.obj (N b)] :=
    GroupBaseChange.Construction.descended_inv_image F G H c (M b) (d b) (hab b).2.2
  let groupN (b : β) := GroupReflection.Construction.groupObjectOfMappedOperations G (N b) (one b) (mul b) (d b)
    (hOne b) (hMul b) (hInv b) (hInject b _) (hInject b _) (hInject b _) (hInject b _)
  refine ⟨t, h, groupN, fun b ↦ ⟨?_, ?_⟩⟩
  · exact GroupReflection.Construction.groupObjectOfMappedOperations_comm G (N b) (one b) (mul b) (d b)
      (hOne b) (hMul b) (hInv b) (hInject b _) (hInject b _) (hInject b _) (hInject b _) (hInject b _)
  · exact GroupReflection.Construction.groupObjectOfMappedOperations_image G (N b) (one b) (mul b) (d b)
      (hOne b) (hMul b) (hInv b) (hInject b _) (hInject b _) (hInject b _) (hInject b _)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteGroups.Construction
