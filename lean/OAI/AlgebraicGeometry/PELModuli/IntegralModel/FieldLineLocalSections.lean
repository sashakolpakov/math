import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldSectionModules
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleOn
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.LinearAlgebra.DFinsupp
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CanonicalChartSections
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldAffineSections

/-! # Field Line Local Sections -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldLineLocalSections

noncomputable section

/-! Generic affine and line-bundle base change, isolated from the Openness
statement-dependent group-theoretic import chain. All constructions below
are proved here and retain the actual scheme-module section maps. -/

/-! Flatness of the actual line-bundle coefficient modules on trivializing affine opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

namespace FieldBaseChange

universe u

def lineBundleSectionsTrivialization {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj M ≅
      (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) :=
  (SheafOfModules.evaluation (X.ringCatSheaf.over U) (op (Over.mk (𝟙 U)))).mapIso
    (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent.Construction.lineBundleOverTrivialization U e)

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (M : X.Modules) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)

def baseRingLineBundleSectionsIso :
    ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op U) ≅
      ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)).obj.obj (op U) :=
  (ModuleCat.restrictScalars (FieldSectionModules.FieldBaseChange.baseRingSectionConstants f U)).mapIso
    (lineBundleSectionsTrivialization U e)

include e in
theorem baseRingLineBundleSections_flat [Flat f] (hU : IsAffineOpen U) :
    Module.Flat R (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op U)) := by
  have hflat := FieldSectionModules.FieldBaseChange.baseRingStructureSections_flat f U hU
  exact Module.Flat.of_linearEquiv (baseRingLineBundleSectionsIso f M U e).toLinearEquiv

end FieldBaseChange

/-! The first three Cech terms for a line bundle on a flat separated family are flat over the base. -/

namespace FieldBaseChange

universe u v

theorem flat_finite_product_modules (R : Type u) [CommRing R] {ι : Type v} [Fintype ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] : Module.Flat R (∀ i, M i) :=
  Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := R)).symm

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [Flat f] [IsSeparated f] (M : X.Modules) (U : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleOn.Construction.LineBundleAffineCover M)

omit [Flat f] in
include f in
theorem affine_inter_of_separated_base (V W : X.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    IsAffineOpen (V ⊓ W) :=
  (isAffineHom_diagonal_iff (f := f)).mp inferInstance ⊤ (isAffineOpen_top _)
    V (by simp) W (by simp) hV hW

omit [IsSeparated f] in
theorem lineBundleCech_flat_zero : Module.Flat R (FieldSectionModules.FieldBaseChange.schemeModuleCechShortComplex f M U.opens).X₁ := by
  have hflat (i : U.index) :
      Module.Flat R (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op (U.opens i))) :=
    baseRingLineBundleSections_flat f M (U.opens i) (U.trivialization i) (U.affine i)
  exact flat_finite_product_modules R _

theorem lineBundleCech_flat_one : Module.Flat R (FieldSectionModules.FieldBaseChange.schemeModuleCechShortComplex f M U.opens).X₂ := by
  have hflat (i j : U.index) :
      Module.Flat R (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op (U.opens i ⊓ U.opens j))) :=
    baseRingLineBundleSections_flat f M (U.opens i ⊓ U.opens j)
      (U.trivializationOn i _ inf_le_left)
      (affine_inter_of_separated_base f _ _ (U.affine i) (U.affine j))
  have hcol (i : U.index) : Module.Flat R
      (∀ j : U.index, ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op (U.opens i ⊓ U.opens j))) :=
    flat_finite_product_modules R _
  exact flat_finite_product_modules R _

theorem lineBundleCech_flat_two : Module.Flat R (FieldSectionModules.FieldBaseChange.schemeModuleCechShortComplex f M U.opens).X₃ := by
  have hflat (i j k : U.index) : Module.Flat R
      (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op ((U.opens i ⊓ U.opens j) ⊓ U.opens k))) :=
    baseRingLineBundleSections_flat f M ((U.opens i ⊓ U.opens j) ⊓ U.opens k)
      (U.trivializationOn i _ (inf_le_left.trans inf_le_left))
      (affine_inter_of_separated_base f _ _
        (affine_inter_of_separated_base f _ _ (U.affine i) (U.affine j)) (U.affine k))
  have hcol (i j : U.index) : Module.Flat R
      (∀ k : U.index, ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj
        (op ((U.opens i ⊓ U.opens j) ⊓ U.opens k))) := flat_finite_product_modules R _
  have hrow (i : U.index) : Module.Flat R
      (∀ j k : U.index, ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj
        (op ((U.opens i ⊓ U.opens j) ⊓ U.opens k))) := flat_finite_product_modules R _
  exact flat_finite_product_modules R _

theorem exists_flat_lineBundleCech [QuasiCompact f] (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) :
    ∃ U : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleOn.Construction.LineBundleAffineCover M,
      Module.Flat R (FieldSectionModules.FieldBaseChange.schemeModuleCechShortComplex f M U.opens).X₁ ∧
      Module.Flat R (FieldSectionModules.FieldBaseChange.schemeModuleCechShortComplex f M U.opens).X₂ ∧
      Module.Flat R (FieldSectionModules.FieldBaseChange.schemeModuleCechShortComplex f M U.opens).X₃ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨U⟩ := ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleOn.Construction.exists_lineBundleAffineCover M hM
  exact ⟨U, lineBundleCech_flat_zero f M U, lineBundleCech_flat_one f M U, lineBundleCech_flat_two f M U⟩

end FieldBaseChange

/-! Canonical affine base change of the actual sections of a line bundle on a trivializing chart. -/

open _root_.CategoryTheory.Limits
open scoped TensorProduct

namespace FieldBaseChange

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (M : X.Modules) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)

def baseRingModuleChartSectionsEquiv :
    ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op U) ≃ₗ[R]
      ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)).obj.obj (op U) where
  __ := ArithmeticGeometry.OrdinaryLocus.Openness.CanonicalChartSections.Construction.moduleChartSectionsAddEquiv U e
  map_smul' r m := ArithmeticGeometry.OrdinaryLocus.Openness.CanonicalChartSections.Construction.moduleChartSectionsAddEquiv_smul U e (FieldSectionModules.FieldBaseChange.baseRingSectionConstants f U r) m

variable (K : Type u) [CommRing K] [Algebra R K]

def affineBaseChangeModuleSection :
    ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op U) →+
      ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf (pullback.snd f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj
        ((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M)).obj.obj
          (op (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen K f U)) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.PullbackSectionCompatibility.Construction.modulePullbackSectionLE (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) M U
    (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen K f U) inf_le_left

def affineBaseChangeLineBundleSectionsEquiv (hU : IsAffineOpen U) :
    (K ⊗[R] (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op U))) ≃ₗ[K]
      ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf (pullback.snd f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj
        ((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M)).obj.obj
          (op (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen K f U)) :=
  ((baseRingModuleChartSectionsEquiv f M U e).baseChange R K _ _).trans
    ((FieldAffineSections.FieldBaseChange.affineBaseChangeStructureSectionsEquiv K f U hU).trans
      (baseRingModuleChartSectionsEquiv (pullback.snd f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))
        ((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M)
        (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen K f U)
        (ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleCharts.Construction.pullbackLineBundleChart (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) M U
          (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen K f U) inf_le_left e)).symm)

theorem affineBaseChangeLineBundleSectionsEquiv_tmul (hU : IsAffineOpen U)
    (a : K) (m : ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op U)) :
    affineBaseChangeLineBundleSectionsEquiv f M U e K hU (a ⊗ₜ[R] m) =
      a • affineBaseChangeModuleSection f M U K m := by
  let t := baseRingModuleChartSectionsEquiv (pullback.snd f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))
    ((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M)
    (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen K f U)
    (ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleCharts.Construction.pullbackLineBundleChart (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) M U
      (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen K f U) inf_le_left e)
  rw [affineBaseChangeLineBundleSectionsEquiv, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
  apply t.symm_apply_eq.mpr
  rw [t.map_smul, FieldAffineSections.FieldBaseChange.affineBaseChangeStructureSectionsEquiv_tmul]
  have hc := ArithmeticGeometry.OrdinaryLocus.Openness.CanonicalChartSections.Construction.moduleChartSectionsEquiv_pullback U e (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))
    (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen K f U) inf_le_left m
  change (FieldAffineSections.FieldBaseChange.baseRingProductLeftMap f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K) U ⊤)
      (ArithmeticGeometry.OrdinaryLocus.Openness.CanonicalChartSections.Construction.moduleChartSectionsEquiv U e m) *
      FieldAffineSections.FieldBaseChange.baseRingProductRightMap f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K) U ⊤ ((Scheme.ΓSpecIso (.of K)).inv a) =
    FieldSectionModules.FieldBaseChange.baseRingSectionConstants (pullback.snd f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen K f U) a *
      ArithmeticGeometry.OrdinaryLocus.Openness.CanonicalChartSections.Construction.moduleChartSectionsEquiv (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen K f U)
        (ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleCharts.Construction.pullbackLineBundleChart (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) M U
          (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen K f U) inf_le_left e)
        (ArithmeticGeometry.OrdinaryLocus.Openness.PullbackSectionCompatibility.Construction.modulePullbackSectionLE (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) M U
          (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen K f U) inf_le_left m)
  rw [hc]
  exact mul_comm _ _

end FieldBaseChange

/-! Line-bundle section base change on inverse-image opens, compatible with restriction. -/

namespace FieldBaseChange

universe u

variable {R : Type u} (K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules)

def affineBaseChangePreimageSection (U : X.Opens) :
    ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op U) →+
      ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf (pullback.snd f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj
        ((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M)).obj.obj
          (op ((pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) ⁻¹ᵁ U)) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.OpenPullbackSections.Construction.modulePullbackSection (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) M U

def affineBaseChangeLineBundlePreimageEquiv (U : X.Opens) (hU : IsAffineOpen U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    (K ⊗[R] (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op U))) ≃ₗ[K]
      ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf (pullback.snd f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj
        ((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M)).obj.obj
          (op ((pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) ⁻¹ᵁ U)) := by
  let F := (FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf (pullback.snd f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj
    ((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M)
  exact (affineBaseChangeLineBundleSectionsEquiv f M U e K hU).trans
    (F.obj.mapIso (eqToIso (congrArg op (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen_eq_preimage K f U)))).toLinearEquiv

theorem affineBaseChangeLineBundlePreimageEquiv_tmul (U : X.Opens) (hU : IsAffineOpen U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (a : K) (m : ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op U)) :
    affineBaseChangeLineBundlePreimageEquiv K f M U hU e (a ⊗ₜ[R] m) =
      a • affineBaseChangePreimageSection K f M U m := by
  let F := (FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf (pullback.snd f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj
    ((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M)
  let j := eqToHom (congrArg op (FieldAffineSections.FieldBaseChange.affineBaseChangedOpen_eq_preimage K f U))
  change F.obj.map j (affineBaseChangeLineBundleSectionsEquiv f M U e K hU (a ⊗ₜ[R] m)) = _
  rw [affineBaseChangeLineBundleSectionsEquiv_tmul, map_smul]
  apply congrArg (fun x : F.obj.obj (op ((pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) ⁻¹ᵁ U)) ↦ a • x)
  change ((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M).presheaf.map j
    (((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M).presheaf.map
      (homOfLE inf_le_left).op (ArithmeticGeometry.OrdinaryLocus.Openness.OpenPullbackSections.Construction.modulePullbackSection (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) M U m)) =
    ArithmeticGeometry.OrdinaryLocus.Openness.OpenPullbackSections.Construction.modulePullbackSection (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) M U m
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  change ((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M).presheaf.map
    (𝟙 (op ((pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) ⁻¹ᵁ U)))
      (ArithmeticGeometry.OrdinaryLocus.Openness.OpenPullbackSections.Construction.modulePullbackSection (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) M U m) = _
  simp

theorem affineBaseChangePreimageSection_restrict {U V : X.Opens} (i : V ⟶ U)
    (m : ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op U)) :
    affineBaseChangePreimageSection K f M V (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.map i.op m) =
      ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf (pullback.snd f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj
        ((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M)).obj.map
          ((TopologicalSpace.Opens.map (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)).base).map i).op
            (affineBaseChangePreimageSection K f M U m) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.PullbackSectionCompatibility.Construction.modulePullbackSection_restrict (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) M i m

theorem affineBaseChangeLineBundlePreimageEquiv_restrict {U V : X.Opens} (i : V ⟶ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (eU : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (eV : (Scheme.Modules.pullback V.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule V.toScheme)
    (z : K ⊗[R] (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op U))) :
    affineBaseChangeLineBundlePreimageEquiv K f M V hV eV
      ((((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.map i.op).hom.baseChange K z) =
      ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf (pullback.snd f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj
        ((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M)).obj.map
          ((TopologicalSpace.Opens.map (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)).base).map i).op
            (affineBaseChangeLineBundlePreimageEquiv K f M U hU eU z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a m =>
    change affineBaseChangeLineBundlePreimageEquiv K f M V hV eV
      (a ⊗ₜ[R] (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.map i.op m)) = _
    rw [affineBaseChangeLineBundlePreimageEquiv_tmul,
      affineBaseChangeLineBundlePreimageEquiv_tmul, map_smul,
      affineBaseChangePreimageSection_restrict]

end FieldBaseChange

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldLineLocalSections
