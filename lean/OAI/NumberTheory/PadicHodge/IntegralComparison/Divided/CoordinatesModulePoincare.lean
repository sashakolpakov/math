import OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesModuleComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesPoincare

/-! # Coordinates Module Poincare -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesModulePoincare

noncomputable section

/-!
# IntegralComparison: comparison of the relative module complex with its additive resolution

Forgetting the original base scalars identifies the actual module form
complex and its source with the verified additive constructions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesForms

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (σ : Type u)

def forgetFunctor :
    ((BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ((BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat B) AddCommGrpCat)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesModulePoincare.forgetFunctor (p := p) (B := B) (J := J) (δ := δ) (f := f)
local notation "KM" => OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesModuleComplex.complex (p := p) (B := B) (J := J) (δ := δ) (f := f) σ
local notation "KA" => OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesDeRham.complex (p := p) (B := B) (J := J) (δ := δ) (f := f) σ
local notation "AM" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) f
local notation "AA" => OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesDeRham.ambientPresheaf (p := p) (B := B) (J := J) (δ := δ) (f := f)

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

def formsIso (n : ℕ) : (F).obj (CoordinatesModuleMaps.formsPresheaf σ n) ≅
    CoordinatesForms.formsPresheaf σ n :=
  NatIso.ofComponents (fun U => (AddEquiv.refl (CoordinatesForms.Forms σ U.unop n)).toAddCommGrpIso) (by
    intro U V α
    apply AddCommGrpCat.hom_ext
    ext ω
    rfl)

def ambientIso : (F).obj AM ≅ AA :=
  NatIso.ofComponents (fun U => (AddEquiv.refl U.unop.ring).toAddCommGrpIso) (by
    intro U V α
    apply AddCommGrpCat.hom_ext
    ext a
    rfl)

def complexIso : ((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj KM ≅ KA :=
  HomologicalComplex.Hom.isoOfComponents (formsIso σ) (by
    intro n m h
    change n + 1 = m at h
    subst m
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    ext ω
    change ((KA).d n (n + 1)).app U ω = ((KM).d n (n + 1)).app U ω
    rw [CoordinatesDeRham.complex_d]
    erw [CoordinatesModuleComplex.complex_d]
    rfl)

def sourceIso :
    ((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ _).obj AM) ≅
      (CochainComplex.single₀ _).obj AA :=
  (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).app AM ≪≫
    (CochainComplex.single₀ _).mapIso ambientIso

omit [Fact p.Prime] in
theorem sourceIso_inv_zero :
    (sourceIso (p := p) (B := B) (J := J) (δ := δ) (f := f)).inv.f 0 = (ambientIso).inv := by
  change ((CochainComplex.single₀ _).map (ambientIso).inv).f 0 ≫
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).inv.app AM).f 0 = _
  rw [CochainComplex.single₀_map_f_zero, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
  rfl

def transportedAugmentation : (CochainComplex.single₀ _).obj AA ⟶ KA :=
  (sourceIso).inv ≫ ((F).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (CoordinatesModuleComplex.augmentation σ) ≫ (complexIso σ).hom

theorem transportedAugmentation_zero :
    (transportedAugmentation (p := p) (B := B) (J := J) (δ := δ) (f := f) σ).f 0 =
      CoordinatesDeRham.augmentationZero σ := by
  change (sourceIso).inv.f 0 ≫
    (((F).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (CoordinatesModuleComplex.augmentation σ)).f 0 ≫
    (complexIso σ).hom.f 0 = CoordinatesDeRham.augmentationZero σ
  rw [sourceIso_inv_zero]
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext a
  change ((CoordinatesModuleComplex.augmentation σ).f 0).app U a =
    CoordinatesDeRham.constants σ U.unop a
  rw [CoordinatesModuleComplex.augmentation_zero]
  exact CoordinatesModuleComplex.constantsLinear_apply σ U.unop a

theorem augmentation_comparison :
    transportedAugmentation (p := p) (B := B) (J := J) (δ := δ) (f := f) σ =
      CoordinatesDeRham.augmentation σ := by
  apply HomologicalComplex.from_single_hom_ext
  exact (transportedAugmentation_zero σ).trans (CoordinatesDeRham.augmentation_zero σ).symm

/-- The actual module augmentation over the original crystalline base is a quasi-isomorphism. -/
instance augmentation_quasiIso [Fintype σ] :
    QuasiIso (CoordinatesModuleComplex.augmentation (p := p) (B := B) (J := J) (δ := δ) (f := f) σ) := by
  have h : QuasiIso (transportedAugmentation (p := p) (B := B) (J := J) (δ := δ) (f := f) σ) := by
    rw [augmentation_comparison]
    infer_instance
  have hm : QuasiIso (((F).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (CoordinatesModuleComplex.augmentation σ)) :=
    (quasiIso_iff_comp_right _ (complexIso σ).hom).mp
      ((quasiIso_iff_comp_left (sourceIso).inv _).mp h)
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ F).mp hm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesModulePoincare
