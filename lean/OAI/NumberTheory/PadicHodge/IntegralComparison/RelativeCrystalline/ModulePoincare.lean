import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Poincare

/-! # Module Poincare -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModulePoincare

noncomputable section

/-!
# IntegralComparison: exactness of relative frame resolutions with the original coefficients
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)

def forgetFunctor : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat B) AddCommGrpCat)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModulePoincare.forgetFunctor (C := C) (B := B)
local notation "KM" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex.complex H Q π
local notation "KA" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormComplex.complex H Q π
local notation "AM" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex.ambientPresheaf Q
local notation "AA" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Augmentation.ambientPresheaf Q

instance forgetFunctor_additive : (F).Additive := by
  dsimp [forgetFunctor]
  infer_instance

instance forgetFunctor_preservesHomology : (F).PreservesHomology := by
  let : PreservesLimitsOfSize.{0, 0} F := by dsimp [forgetFunctor]; infer_instance
  let : PreservesColimitsOfSize.{0, 0} F := by dsimp [forgetFunctor]; infer_instance
  infer_instance

instance forgetFunctor_reflectsIsomorphisms : (F).ReflectsIsomorphisms := by
  dsimp [forgetFunctor]
  infer_instance

def formsIso (n : ℕ) : (F).obj (ModuleMaps.formsPresheaf H Q π n) ≅
    FormComplex.formsPresheaf H Q π n :=
  NatIso.ofComponents (fun U => (AddEquiv.refl (FormData.Forms H Q π U.unop n)).toAddCommGrpIso) (by
    intro U V α
    apply AddCommGrpCat.hom_ext
    ext ω
    rfl)

def ambientIso : (F).obj AM ≅ AA :=
  NatIso.ofComponents (fun U => (AddEquiv.refl (Q.obj U.unop).ring).toAddCommGrpIso) (by
    intro U V α
    apply AddCommGrpCat.hom_ext
    ext a
    rfl)

def complexIso : ((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj KM ≅ KA :=
  HomologicalComplex.Hom.isoOfComponents (formsIso H Q π) (by
    intro n m h
    change n + 1 = m at h
    subst m
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    ext ω
    change ((KA).d n (n + 1)).app U ω = ((KM).d n (n + 1)).app U ω
    rw [FormComplex.complex_d]
    erw [ModuleComplex.complex_d]
    rfl)

def sourceIso :
    ((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ _).obj AM) ≅
      (CochainComplex.single₀ _).obj AA :=
  (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).app AM ≪≫
    (CochainComplex.single₀ _).mapIso (ambientIso Q)

theorem sourceIso_inv_zero : (sourceIso Q).inv.f 0 = (ambientIso Q).inv := by
  change ((CochainComplex.single₀ _).map (ambientIso Q).inv).f 0 ≫
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).inv.app AM).f 0 = _
  rw [CochainComplex.single₀_map_f_zero, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
  rfl

def transportedAugmentation : (CochainComplex.single₀ _).obj AA ⟶ KA :=
  (sourceIso Q).inv ≫ ((F).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (ModuleComplex.augmentation H Q π) ≫ (complexIso H Q π).hom

theorem transportedAugmentation_zero : (transportedAugmentation H Q π).f 0 =
    Augmentation.augmentationZero H Q π := by
  change (sourceIso Q).inv.f 0 ≫
    (((F).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (ModuleComplex.augmentation H Q π)).f 0 ≫
    (complexIso H Q π).hom.f 0 = Augmentation.augmentationZero H Q π
  rw [sourceIso_inv_zero]
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext a
  change ((ModuleComplex.augmentation H Q π).f 0).app U a =
    Augmentation.constants H Q π U.unop a
  rw [ModuleComplex.augmentation_zero]
  exact ModuleComplex.constantsLinear_apply H Q π U.unop a

theorem augmentation_comparison : transportedAugmentation H Q π =
    Augmentation.augmentation H Q π := by
  apply HomologicalComplex.from_single_hom_ext
  exact (transportedAugmentation_zero H Q π).trans
    (Augmentation.augmentation_zero H Q π).symm

variable [Fact p.Prime] (σ : Type u) [Fintype σ]

theorem augmentation_quasiIso
    (h : ∀ U, ∃ e : Crystalline.DividedCoordinates.object (Q.obj U) σ ≅ H.obj U,
      e.hom ≫ π.app U = Crystalline.DividedCoordinates.projection (Q.obj U) σ) :
    QuasiIso (ModuleComplex.augmentation H Q π) := by
  have ha : QuasiIso (transportedAugmentation H Q π) := by
    rw [augmentation_comparison]
    exact Poincare.augmentation_quasiIso H Q π σ h
  have hm : QuasiIso (((F).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (ModuleComplex.augmentation H Q π)) :=
    (quasiIso_iff_comp_right _ (complexIso H Q π).hom).mp
      ((quasiIso_iff_comp_left (sourceIso Q).inv _).mp ha)
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ F).mp hm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModulePoincare
