import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorBifunctor

/-! # Tensor Composition -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorComposition.Construction

noncomputable section

/-! Compatibility of tensor comparisons with composition of scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

local instance tensorCompositionMonoidal (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

theorem moduleSheafificationUnit_pushforwardTensor {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M N : X.Modules) :
    SheafRestriction.Construction.moduleSheafificationUnit
        (((Scheme.Modules.pushforward f).obj M).val ⊗
          ((Scheme.Modules.pushforward f).obj N).val) ≫
        (TensorFunctoriality.Construction.pushforwardSheafTensorMap f M N).val =
      TensorFunctoriality.Construction.pushforwardPresheafTensorMap f M.val N.val ≫
        (TensorFunctoriality.Construction.pushforwardModulePresheaf f).map (SheafRestriction.Construction.moduleSheafificationUnit (M.val ⊗ N.val)) := by
  rw [← TensorUnit.Construction.sheafTensorHomEquiv_apply_eq, TensorFunctoriality.Construction.pushforwardSheafTensorMap, Equiv.apply_symm_apply]
  rfl

theorem pushforwardSheafTensorMap_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M N : X.Modules) :
    TensorFunctoriality.Construction.sheafTensorMap ((Scheme.Modules.pushforwardComp f g).hom.app M)
        ((Scheme.Modules.pushforwardComp f g).hom.app N) ≫
        TensorFunctoriality.Construction.pushforwardSheafTensorMap (f ≫ g) M N =
      TensorFunctoriality.Construction.pushforwardSheafTensorMap g ((Scheme.Modules.pushforward f).obj M)
          ((Scheme.Modules.pushforward f).obj N) ≫
        (Scheme.Modules.pushforward g).map (TensorFunctoriality.Construction.pushforwardSheafTensorMap f M N) ≫
          (Scheme.Modules.pushforwardComp f g).hom.app (SheafTensor.Construction.sheafTensor M N) := by
  apply (SheafTensor.Construction.sheafTensorHomEquiv _ _ _).injective
  rw [TensorFunctoriality.Construction.sheafTensorHomEquiv_naturality_left, TensorFunctoriality.Construction.sheafTensorHomEquiv_naturality_right]
  dsimp only [Functor.comp_obj]
  simp only [TensorFunctoriality.Construction.pushforwardSheafTensorMap, Equiv.apply_symm_apply]
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  let V := g ⁻¹ᵁ U.unop
  let m' : ((Scheme.Modules.pushforward f).obj M).val.obj (.op V) := m
  let n' : ((Scheme.Modules.pushforward f).obj N).val.obj (.op V) := n
  have h := congrArg (fun a ↦ a.app (.op V)) (moduleSheafificationUnit_pushforwardTensor f M N)
  exact congrArg (fun a ↦ a (m' ⊗ₜ[Γ(Y, V)] n')) h.symm

theorem pullbackTensorSquare_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (TwoSquare.vComp (TensorBifunctor.Construction.pullbackTensorSquare g) (TensorBifunctor.Construction.pullbackTensorSquare f)).whiskerRight
        (Scheme.Modules.pullbackComp f g).inv =
      (TensorBifunctor.Construction.pullbackTensorSquare (f ≫ g)).whiskerLeft
        (NatTrans.prod (Scheme.Modules.pullbackComp f g).inv
          (Scheme.Modules.pullbackComp f g).inv) := by
  apply (mateEquiv
    ((TensorBifunctor.Construction.productAdjunction (Scheme.Modules.pullbackPushforwardAdjunction g)
      (Scheme.Modules.pullbackPushforwardAdjunction g)).comp
      (TensorBifunctor.Construction.productAdjunction (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackPushforwardAdjunction f)))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))).injective
  rw [mateEquiv_conjugateEquiv_vcomp, Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    mateEquiv_hcomp, TensorBifunctor.Construction.mate_pullbackTensorSquare, TensorBifunctor.Construction.mate_pullbackTensorSquare,
    conjugateEquiv_mateEquiv_vcomp, TensorBifunctor.Construction.conjugateEquiv_product_pullbackComp_inv,
    TensorBifunctor.Construction.mate_pullbackTensorSquare]
  apply TwoSquare.ext
  intro M
  simpa only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
    TensorBifunctor.Construction.pushforwardTensorSquare, TensorBifunctor.Construction.pushforwardTensorNat, TensorBifunctor.Construction.tensorSheafFunctor,
    NatTrans.prod, Functor.prod, TwoSquare.mk, TwoSquare.natTrans,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_id,
    Category.id_comp, Category.comp_id, Functor.comp_obj, Category.assoc]
    using (pushforwardSheafTensorMap_comp f g M.1 M.2).symm

theorem pullbackSheafTensorMap_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    (Scheme.Modules.pullbackComp f g).inv.app (SheafTensor.Construction.sheafTensor M N) ≫
        (Scheme.Modules.pullback f).map (TensorFunctoriality.Construction.pullbackSheafTensorMap g M N) ≫
          TensorFunctoriality.Construction.pullbackSheafTensorMap f ((Scheme.Modules.pullback g).obj M)
            ((Scheme.Modules.pullback g).obj N) =
      TensorFunctoriality.Construction.pullbackSheafTensorMap (f ≫ g) M N ≫
        TensorFunctoriality.Construction.sheafTensorMap ((Scheme.Modules.pullbackComp f g).inv.app M)
          ((Scheme.Modules.pullbackComp f g).inv.app N) := by
  have h := congrArg (fun a ↦ a.app (M, N)) (pullbackTensorSquare_comp f g)
  simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TensorBifunctor.Construction.pullbackTensorSquare, TensorBifunctor.Construction.pullbackTensorNat, TensorBifunctor.Construction.tensorSheafFunctor,
    NatTrans.prod, Functor.prod, TwoSquare.mk, TwoSquare.natTrans,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_id,
    Category.id_comp, Category.comp_id, Functor.comp_obj, Category.assoc] using h

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorComposition.Construction
