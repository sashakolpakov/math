import OAI.ArithmeticGeometry.Models.SpreadingOut.GroupOperationDescent
import OAI.ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness

/-! # Group -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Group.Construction

noncomputable section

/-! Commutative group structures on smooth proper coefficient models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.NumberField

universe u

theorem smooth_over_tensor {S : Scheme.{u}} (M N : Over S)
    [Smooth M.hom] [Smooth N.hom] : Smooth (M ⊗ N).hom := by
  change Smooth (pullback.fst M.hom N.hom ≫ M.hom)
  infer_instance

theorem commutative_group_model_after_enlargement
    {K : Type u} [Field K] {s : Finset K}
    (M : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) [Smooth M.hom] [IsProper M.hom]
    [GrpObj ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj M)]
    [IsCommMonObj ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj M)] :
    ∃ (t : Finset K) (h : s ⊆ t),
      let F := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
      let G := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)
      let N := F.obj M
      ∃ groupN : GrpObj N,
        (letI := groupN; IsCommMonObj N) ∧
        (letI := groupN
         Functor.grpObjObj (F := G) (G := N) =
           GrpObj.ofIso ((GenericMorphisms.Construction.coefficientGenericComparison h).app M).symm) := by
  obtain ⟨t, h, one, mul, inv, hOne, hMul, hInv⟩ := GroupOperationDescent.Construction.group_operations_descend M
  let F := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
  let G := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)
  let N := F.obj M
  let genericGroup : GrpObj (G.obj N) :=
    GrpObj.ofIso ((GenericMorphisms.Construction.coefficientGenericComparison h).app M).symm
  have : IsCommMonObj (G.obj N) :=
    GroupReflection.Construction.commutative_group_of_iso ((GenericMorphisms.Construction.coefficientGenericComparison h).app M).symm
  have : Smooth N.hom := inferInstanceAs (Smooth (pullback.snd M.hom _))
  have : IsProper N.hom := inferInstanceAs (IsProper (pullback.snd M.hom _))
  have : Smooth (𝟙_ (Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K t))).hom :=
    inferInstanceAs (Smooth (𝟙 _))
  have : Smooth (N ⊗ N).hom := smooth_over_tensor N N
  have : Smooth ((𝟙_ (Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K t))) ⊗ N).hom :=
    smooth_over_tensor _ N
  have : Smooth (N ⊗ (𝟙_ (Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K t)))).hom :=
    smooth_over_tensor N _
  have : Smooth ((N ⊗ N) ⊗ N).hom := smooth_over_tensor _ N
  have hInject (Y : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K t)) [Smooth Y.hom] :
      Function.Injective (G.map : (Y ⟶ N) → _) :=
    GenericFaithfulness.Construction.generic_pullback_map_injective (algebraMap (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K t) K)
      Subtype.val_injective
  let groupN := GroupReflection.Construction.groupObjectOfMappedOperations G N one mul inv hOne hMul hInv
    (hInject _) (hInject _) (hInject _) (hInject _)
  refine ⟨t, h, groupN, ?_, ?_⟩
  · exact GroupReflection.Construction.groupObjectOfMappedOperations_comm G N one mul inv hOne hMul hInv
      (hInject _) (hInject _) (hInject _) (hInject _) (hInject _)
  · exact GroupReflection.Construction.groupObjectOfMappedOperations_image G N one mul inv hOne hMul hInv
      (hInject _) (hInject _) (hInject _) (hInject _)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.Group.Construction
