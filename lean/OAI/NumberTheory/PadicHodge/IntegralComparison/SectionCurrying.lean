import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ConstantSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveSectionNaturality

/-! # Section Currying -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SectionCurrying

noncomputable section

/-!
# IntegralComparison: explicit currying for module-valued presheaf sections
-/

open _root_.CategoryTheory Opposite

universe u v

variable {C : Type u} [Category.{v} C] (R : Type u) [CommRing R]
  (M : ModuleCat.{u} R) (F : Cᵒᵖ ⥤ ModuleCat.{u} R)

abbrev sections := (ExhaustiveSectionNaturality.globalSectionsFunctor R (ModuleCat.of R R)).obj F

def curry (a : (Functor.const Cᵒᵖ).obj M ⟶ F) : M ⟶ sections R F :=
  ModuleCat.ofHom
    { toFun := fun x => (Functor.const Cᵒᵖ).map (Module.ConstantSections.elementHom R M x) ≫ a
      map_add' := by
        intro x y
        apply NatTrans.ext
        funext T
        change (Module.ConstantSections.elementHom R M (x + y)) ≫ a.app T = _
        rw [map_add, Preadditive.add_comp]
        rfl
      map_smul' := by
        intro r x
        apply NatTrans.ext
        funext T
        change (Module.ConstantSections.elementHom R M (r • x)) ≫ a.app T = _
        rw [map_smul, Linear.smul_comp]
        rfl }

theorem curry_app (a : (Functor.const Cᵒᵖ).obj M ⟶ F) (x : M) (T : Cᵒᵖ) (r : R) :
    (curry R M F a x).app T r = a.app T (r • x) := rfl

def uncurry (b : M ⟶ sections R F) : (Functor.const Cᵒᵖ).obj M ⟶ F where
  app T := ModuleCat.ofHom
    { toFun := fun x => (b x).app T (1 : R)
      map_add' := by
        intro x y
        change (b.hom (x + y)).app T (1 : R) = _
        rw [map_add]
        rfl
      map_smul' := by
        intro r x
        change (b.hom (r • x)).app T (1 : R) = _
        rw [map_smul]
        rfl }
  naturality T U α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (congrArg (fun f : ModuleCat.of R R ⟶ F.obj U => f (1 : R)) ((b x).naturality α))

theorem uncurry_curry (a : (Functor.const Cᵒᵖ).obj M ⟶ F) : uncurry R M F (curry R M F a) = a := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change a.app T ((1 : R) • x) = a.app T x
  rw [one_smul]

theorem curry_uncurry (b : M ⟶ sections R F) : curry R M F (uncurry R M F b) = b := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change R at r
  change (b.hom (r • x)).app T (1 : R) = (b x).app T r
  rw [map_smul]
  change r • (b x).app T (1 : R) = (b x).app T r
  let l : R →ₗ[R] F.obj T := ((b x).app T).hom
  change r • l 1 = l r
  have hr : (r : R) * (1 : R) = r := @mul_one R _ r
  have hl : l ((r : R) * (1 : R)) = r • l 1 := l.map_smul (r : R) (1 : R)
  exact hl.symm.trans (congrArg l hr)

def equiv : ((Functor.const Cᵒᵖ).obj M ⟶ F) ≃ (M ⟶ sections R F) where
  toFun := curry R M F
  invFun := uncurry R M F
  left_inv := uncurry_curry R M F
  right_inv := curry_uncurry R M F

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SectionCurrying
