import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FormalCoproductForget
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnderlyingAdditiveSheafExactness

/-! # Cosimplicial Forget -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.CosimplicialForget

noncomputable section

open _root_.AlgebraicTopology _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u

/-- Forgetting the base module structure recovers the underlying additive
presheaf of the scheme module. -/
noncomputable def coefficientModulePresheafForgetIso {X : Scheme.{u}} {R : Type u} [CommRing R]
    (ρ : R →+* Γ(X, ⊤)) (M : X.Modules) :
    Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M ⋙ Module.ProductForget.moduleForget R ≅ (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf M).obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Forgetting the base module structure degreewise in the Cech cosimplicial
object recovers the cosimplicial object of the underlying sheaf. -/
noncomputable def coefficientCechCosimplicialIso
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    ((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ U).cech).obj (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M) ⋙
        Module.ProductForget.moduleForget R) ≅
      (FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ U).cech).obj (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf M).obj :=
  Functor.isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
      (FormalCoproductForget.evalOpForgetIso R (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M)) ≪≫
    Functor.isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
      ((FormalCoproduct.evalOp X.Opens AddCommGrpCat.{u}).mapIso
        (coefficientModulePresheafForgetIso ρ M))

@[reassoc]
theorem coefficientCechCosimplicialIso_hom_π
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (q : SimplexCategory)
    (i : (unop ((FormalCoproduct.mk _ U).cech.rightOp.obj q)).I) :
    (coefficientCechCosimplicialIso ρ M U).hom.app q ≫
        Pi.π (fun j => M.presheaf.obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj q)).obj j))) i =
      (Module.ProductForget.moduleForget R).map
        (Pi.π (fun j => (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M).obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj q)).obj j))) i) := by
  change
    ((Functor.isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
          (FormalCoproductForget.evalOpForgetIso R
            (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M))).hom.app q ≫
        (Functor.isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
          ((FormalCoproduct.evalOp X.Opens AddCommGrpCat.{u}).mapIso
            (coefficientModulePresheafForgetIso ρ M))).hom.app q) ≫ _ = _
  erw [Category.assoc]
  have hsecond :
      (Functor.isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
          ((FormalCoproduct.evalOp X.Opens AddCommGrpCat.{u}).mapIso
            (coefficientModulePresheafForgetIso ρ M))).hom.app q ≫
        Pi.π (fun j => M.presheaf.obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj q)).obj j))) i =
      Pi.π (fun j =>
        (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M ⋙ Module.ProductForget.moduleForget R).obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj q)).obj j))) i := by
    change Limits.Pi.map (fun j =>
        (coefficientModulePresheafForgetIso ρ M).hom.app
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj q)).obj j))) ≫ _ = _
    erw [Limits.Pi.map_π]
    rfl
  erw [hsecond]
  change (FormalCoproductForget.evalOpForgetIso R
      (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M)).hom.app
        ((FormalCoproduct.mk _ U).cech.rightOp.obj q) ≫ _ = _
  exact FormalCoproductForget.evalOpForgetIso_hom_π R
    (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M)
    ((FormalCoproduct.mk _ U).cech.rightOp.obj q) i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.CosimplicialForget
