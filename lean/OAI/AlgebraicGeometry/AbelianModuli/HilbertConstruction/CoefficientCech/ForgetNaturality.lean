import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ScalarMaps

/-! # Forget Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ForgetNaturality

noncomputable section

open _root_.AlgebraicTopology _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u

@[reassoc]
theorem cechComplexFunctor_map_f_π
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : (unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
      (SimplexCategory.mk n))).I) :
    ((cechComplexFunctor U).map (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom f).hom).f n ≫
        Pi.π (fun j => N.presheaf.obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj j))) i =
      Pi.π (fun j => M.presheaf.obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj j))) i ≫
        (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom f).hom.app
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj i)) := by
  change Limits.Pi.map (fun j => (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom f).hom.app
      (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
        (SimplexCategory.mk n))).obj j))) ≫ _ = _
  exact Limits.Pi.map_π _ i

/-- The additive comparison obtained by forgetting the base action is
natural in the coefficient module. -/
theorem coefficientCechComplexForgetIso_naturality
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) :
    (((Module.ProductForget.moduleForget R).mapHomologicalComplex (.up ℕ)).map
          ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor ρ U).map f)) ≫
        (ComplexForget.coefficientCechComplexForgetIso ρ N U).hom =
      (ComplexForget.coefficientCechComplexForgetIso ρ M U).hom ≫
        (cechComplexFunctor U).map (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom f).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    ComplexForget.coefficientCechComplexForgetIso_hom_f,
    ComplexForget.coefficientCechComplexForgetIso_hom_f]
  apply Pi.hom_ext
  intro i
  change
    ((Module.ProductForget.moduleForget R).map
          (((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor ρ U).map f).f n) ≫
        (CosimplicialForget.coefficientCechCosimplicialIso ρ N U).hom.app
          (SimplexCategory.mk n)) ≫
      Pi.π (fun j => N.presheaf.obj
        (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
          (SimplexCategory.mk n))).obj j))) i =
    ((CosimplicialForget.coefficientCechCosimplicialIso ρ M U).hom.app
          (SimplexCategory.mk n) ≫
        ((cechComplexFunctor U).map (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom f).hom).f n) ≫
      Pi.π (fun j => N.presheaf.obj
        (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
          (SimplexCategory.mk n))).obj j))) i
  let V := op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
    (SimplexCategory.mk n))).obj i)
  let PM := fun j => ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).obj M).obj
    (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
      (SimplexCategory.mk n))).obj j))
  let PN := fun j => ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).obj N).obj
    (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
      (SimplexCategory.mk n))).obj j))
  let QM := fun j => M.presheaf.obj
    (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
      (SimplexCategory.mk n))).obj j))
  let QN := fun j => N.presheaf.obj
    (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
      (SimplexCategory.mk n))).obj j))
  let a := ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor ρ U).map f).f n
  let bM := (CosimplicialForget.coefficientCechCosimplicialIso ρ M U).hom.app
    (SimplexCategory.mk n)
  let bN := (CosimplicialForget.coefficientCechCosimplicialIso ρ N U).hom.app
    (SimplexCategory.mk n)
  let c := ((cechComplexFunctor U).map (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom f).hom).f n
  let pM := Pi.π PM i
  let pN := Pi.π PN i
  let qM := Pi.π QM i
  let qN := Pi.π QN i
  let d := ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).map f).app V
  let d' := (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom f).hom.app V
  have hbM : bM ≫ qM = (Module.ProductForget.moduleForget R).map pM := by
    exact CosimplicialForget.coefficientCechCosimplicialIso_hom_π ρ M U _ i
  have hbN : bN ≫ qN = (Module.ProductForget.moduleForget R).map pN := by
    exact CosimplicialForget.coefficientCechCosimplicialIso_hom_π ρ N U _ i
  have ha : a ≫ pN = pM ≫ d := by
    exact ScalarMaps.coefficientCechComplexFunctor_map_f_π ρ f U n i
  have hc : c ≫ qN = qM ≫ d' := by
    exact cechComplexFunctor_map_f_π f U n i
  have hd : (Module.ProductForget.moduleForget R).map d = d' := rfl
  have hleft : ((Module.ProductForget.moduleForget R).map a ≫ bN) ≫ qN =
      (Module.ProductForget.moduleForget R).map a ≫ (Module.ProductForget.moduleForget R).map pN :=
    (Category.assoc _ _ _).trans
      (congrArg (fun q => (Module.ProductForget.moduleForget R).map a ≫ q) hbN)
  have hmiddle :
      (Module.ProductForget.moduleForget R).map a ≫ (Module.ProductForget.moduleForget R).map pN =
        (Module.ProductForget.moduleForget R).map pM ≫ (Module.ProductForget.moduleForget R).map d :=
    ((Module.ProductForget.moduleForget R).map_comp a pN).symm.trans
      ((congrArg (Module.ProductForget.moduleForget R).map ha).trans
        ((Module.ProductForget.moduleForget R).map_comp pM d))
  have hright :
      (Module.ProductForget.moduleForget R).map pM ≫ (Module.ProductForget.moduleForget R).map d =
        (bM ≫ c) ≫ qN :=
    (congrArg (fun q => (Module.ProductForget.moduleForget R).map pM ≫ q) hd).trans
      ((congrArg (fun q => q ≫ d') hbM.symm).trans
        ((Category.assoc bM qM d').trans
          ((congrArg (fun q => bM ≫ q) hc.symm).trans
            (Category.assoc bM c qN).symm)))
  change ((Module.ProductForget.moduleForget R).map a ≫ bN) ≫ qN =
    (bM ≫ c) ≫ qN
  exact hleft.trans (hmiddle.trans hright)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ForgetNaturality
