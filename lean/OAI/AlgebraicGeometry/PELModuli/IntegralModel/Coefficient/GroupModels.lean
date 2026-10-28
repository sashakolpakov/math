import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GroupOperationDescent
import OAI.ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness

/-! # Group Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GroupModels.Coefficients

noncomputable section

/-! Generalization of the proved GroupModels construction to a
general coefficient ring for smooth proper complex group-scheme families.

 Commutative group structures on smooth proper coefficient models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.NumberField

universe u

open OAI.ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness.Construction

theorem smooth_over_tensor {S : Scheme.{u}} (M N : Over S)
    [Smooth M.hom] [Smooth N.hom] : Smooth (M ⊗ N).hom := by
  change Smooth (pullback.fst M.hom N.hom ≫ M.hom)
  infer_instance

theorem commutative_group_model_after_enlargement
    {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K] {s : Finset K}
    (M : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)) [Smooth M.hom] [IsProper M.hom]
    [GrpObj ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)).obj M)]
    [IsCommMonObj ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)).obj M)] :
    ∃ (t : Finset K) (h : s ⊆ t),
      let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K h)
      let G := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K t)
      let N := F.obj M
      ∃ groupN : GrpObj N,
        (letI := groupN; IsCommMonObj N) ∧
        (letI := groupN
         Functor.grpObjObj (F := G) (G := N) =
           GrpObj.ofIso ((GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R₀) h).app M).symm) := by
  obtain ⟨t, h, one, mul, inv, hOne, hMul, hInv⟩ := GroupOperationDescent.Coefficients.group_operations_descend M
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K h)
  let G := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K t)
  let N := F.obj M
  let genericGroup : GrpObj (G.obj N) :=
    GrpObj.ofIso ((GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R₀) h).app M).symm
  have : IsCommMonObj (G.obj N) :=
    ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.commutative_group_of_iso ((GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R₀) h).app M).symm
  have : Smooth N.hom := inferInstanceAs (Smooth (pullback.snd M.hom _))
  have : IsProper N.hom := inferInstanceAs (IsProper (pullback.snd M.hom _))
  have : Smooth (𝟙_ (Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K t))).hom :=
    inferInstanceAs (Smooth (𝟙 _))
  have : Smooth (N ⊗ N).hom := smooth_over_tensor N N
  have : Smooth ((𝟙_ (Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K t))) ⊗ N).hom :=
    smooth_over_tensor _ N
  have : Smooth (N ⊗ (𝟙_ (Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K t)))).hom :=
    smooth_over_tensor N _
  have : Smooth ((N ⊗ N) ⊗ N).hom := smooth_over_tensor _ N
  have hInject (Y : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K t)) [Smooth Y.hom] :
      Function.Injective (G.map : (Y ⟶ N) → _) :=
    ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness.Construction.generic_pullback_map_injective (algebraMap (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R₀ K t) K)
      Subtype.val_injective
  let groupN := ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.groupObjectOfMappedOperations G N one mul inv hOne hMul hInv
    (hInject _) (hInject _) (hInject _) (hInject _)
  refine ⟨t, h, groupN, ?_, ?_⟩
  · exact ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.groupObjectOfMappedOperations_comm G N one mul inv hOne hMul hInv
      (hInject _) (hInject _) (hInject _) (hInject _) (hInject _)
  · exact ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.groupObjectOfMappedOperations_image G N one mul inv hOne hMul hInv
      (hInject _) (hInject _) (hInject _) (hInject _)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GroupModels.Coefficients
