import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldSectionModules
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorPushoutCoordinates

/-! # Field Affine Sections -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldAffineSections

noncomputable section

/-! Generic affine and line-bundle base change, isolated from the Openness
statement-dependent group-theoretic import chain. All constructions below
are proved here and retain the actual scheme-module section maps. -/

/-! Affine-product section rings as tensor products over an arbitrary affine base ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

namespace FieldBaseChange

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorPushoutCoordinates.Construction

universe u

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))

abbrev baseRingProductRectangle (U : X.Opens) (V : Y.Opens) : (pullback f g).Opens :=
  (pullback.fst f g) ⁻¹ᵁ U ⊓ (pullback.snd f g) ⁻¹ᵁ V

abbrev baseRingProductLeftMap (U : X.Opens) (V : Y.Opens) :
    Γ(X, U) ⟶ Γ(pullback f g, baseRingProductRectangle f g U V) :=
  (pullback.fst f g).appLE U _ inf_le_left

abbrev baseRingProductRightMap (U : X.Opens) (V : Y.Opens) :
    Γ(Y, V) ⟶ Γ(pullback f g, baseRingProductRectangle f g U V) :=
  (pullback.snd f g).appLE V _ inf_le_right

theorem baseRingProductSections_isPushout (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsPushout (CommRingCat.ofHom (algebraMap R (FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra f U)))
      (CommRingCat.ofHom (algebraMap R (FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra g V)))
      (baseRingProductLeftMap f g U V) (baseRingProductRightMap f g U V) := by
  let H := IsPullback.of_hasPullback f g
  have hp := (isIso_pushoutSection_iff H (show V ≤ g ⁻¹ᵁ ⊤ by simp)
    (show U ≤ f ⁻¹ᵁ ⊤ by simp) (rfl : baseRingProductRectangle f g U V = _)).mp
      (isIso_pushoutSection_of_isAffineOpen H (show V ≤ g ⁻¹ᵁ ⊤ by simp)
        (show U ≤ f ⁻¹ᵁ ⊤ by simp) rfl (isAffineOpen_top (Spec (.of R))) hV hU)
  refine hp.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  · change f.appLE ⊤ U _ ≫ 𝟙 _ = (Scheme.ΓSpecIso (.of R)).hom ≫
      ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U _)
    simp
  · change g.appLE ⊤ V _ ≫ 𝟙 _ = (Scheme.ΓSpecIso (.of R)).hom ≫
      ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appLE ⊤ V _)
    simp

def baseRingProductSectionsEquiv (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra f U ⊗[R] FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra g V ≃+*
      Γ(pullback f g, baseRingProductRectangle f g U V) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.TensorPushoutCoordinates.Construction.tensorPushoutRingEquiv _ _ _ _ _ (baseRingProductSections_isPushout f g U V hU hV)

theorem baseRingProductSectionsEquiv_tmul (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (x : FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra f U) (y : FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra g V) :
    baseRingProductSectionsEquiv f g U V hU hV (x ⊗ₜ[R] y) =
      baseRingProductLeftMap f g U V x * baseRingProductRightMap f g U V y :=
  ArithmeticGeometry.OrdinaryLocus.Openness.TensorPushoutCoordinates.Construction.tensorPushoutRingEquiv_tmul _ _ _ _ _ _ x y

theorem baseRingProductRectangle_affine (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (baseRingProductRectangle f g U V) := by
  have : IsAffine U := hU
  have : IsAffine V := hV
  have : IsAffine (⊤ : (Spec (.of R)).Opens) := isAffineOpen_top _
  exact .of_isIso
    (Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g)
      (show V ≤ g ⁻¹ᵁ ⊤ by simp) (show U ≤ f ⁻¹ᵁ ⊤ by simp)
      (rfl : baseRingProductRectangle f g U V = _)).isoPullback.hom

end FieldBaseChange

/-! Canonical tensor coordinates for regular functions after affine base change. -/

namespace FieldBaseChange

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorPushoutCoordinates.Construction

universe u

variable (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]

abbrev affineBaseChangeMap : Spec (.of K) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

def baseRingSpecSectionsEquiv :
    FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra (affineBaseChangeMap R K) ⊤ ≃ₐ[R] K where
  __ := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  commutes' r := by
    have h : (Scheme.ΓSpecIso (.of R)).inv ≫ (affineBaseChangeMap R K).appTop ≫
        (Scheme.ΓSpecIso (.of K)).hom = CommRingCat.ofHom (algebraMap R K) := by
      rw [Scheme.ΓSpecIso_naturality]
      exact (Scheme.ΓSpecIso (.of R)).inv_hom_id_assoc _
    exact congrArg (fun q : CommRingCat.of R ⟶ CommRingCat.of K ↦ q r) h

variable {R} {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

abbrev affineBaseChangedOpen (U : X.Opens) : (pullback f (affineBaseChangeMap R K)).Opens :=
  baseRingProductRectangle f (affineBaseChangeMap R K) U ⊤

def affineBaseChangeSectionsRingEquiv (U : X.Opens) (hU : IsAffineOpen U) :
    K ⊗[R] FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra f U ≃+*
      Γ(pullback f (affineBaseChangeMap R K), affineBaseChangedOpen K f U) :=
  (Algebra.TensorProduct.comm R K (FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra f U)).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (S := R) (AlgEquiv.refl (R := R) (A₁ := FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra f U))
      (baseRingSpecSectionsEquiv R K).symm).toRingEquiv.trans
        (baseRingProductSectionsEquiv f (affineBaseChangeMap R K) U ⊤ hU (isAffineOpen_top _)))

theorem affineBaseChangeSectionsRingEquiv_tmul (U : X.Opens) (hU : IsAffineOpen U)
    (a : K) (x : FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra f U) :
    affineBaseChangeSectionsRingEquiv K f U hU (a ⊗ₜ[R] x) =
      baseRingProductLeftMap f (affineBaseChangeMap R K) U ⊤ x *
        baseRingProductRightMap f (affineBaseChangeMap R K) U ⊤ ((Scheme.ΓSpecIso (.of K)).inv a) := by
  change baseRingProductSectionsEquiv f (affineBaseChangeMap R K) U ⊤ hU (isAffineOpen_top _)
    (x ⊗ₜ[R] (baseRingSpecSectionsEquiv R K).symm a) = _
  exact baseRingProductSectionsEquiv_tmul f (affineBaseChangeMap R K) U ⊤ hU (isAffineOpen_top _) x _

def affineBaseChangeSectionsAlgEquiv (U : X.Opens) (hU : IsAffineOpen U) :
    K ⊗[R] FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra f U ≃ₐ[K]
      FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra (pullback.snd f (affineBaseChangeMap R K)) (affineBaseChangedOpen K f U) where
  __ := affineBaseChangeSectionsRingEquiv K f U hU
  commutes' a := by
    change affineBaseChangeSectionsRingEquiv K f U hU (a ⊗ₜ[R] (1 : FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra f U)) =
      FieldSectionModules.FieldBaseChange.baseRingSectionConstants (pullback.snd f (affineBaseChangeMap R K)) (affineBaseChangedOpen K f U) a
    rw [affineBaseChangeSectionsRingEquiv_tmul]
    have h1 : baseRingProductLeftMap f (affineBaseChangeMap R K) U ⊤
        (1 : FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra f U) = 1 :=
      (baseRingProductLeftMap f (affineBaseChangeMap R K) U ⊤).hom.map_one
    rw [h1, one_mul]
    rfl

end FieldBaseChange

/-! Canonical base change of affine structure-sheaf sections as modules over the new base. -/

namespace FieldBaseChange

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorPushoutCoordinates.Construction

universe u

variable {R : Type u} (K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

def affineBaseChangeStructureSectionsEquiv (U : X.Opens) (hU : IsAffineOpen U) :
    (K ⊗[R] (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)).obj.obj (op U))) ≃ₗ[K]
      ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf (pullback.snd f (affineBaseChangeMap R K))).obj
        (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (pullback f (affineBaseChangeMap R K)))).obj.obj
          (op (affineBaseChangedOpen K f U)) :=
  ((FieldSectionModules.FieldBaseChange.baseRingStructureSectionsIso f U).symm.toLinearEquiv.baseChange R K _ _).trans
    ((affineBaseChangeSectionsAlgEquiv K f U hU).toLinearEquiv.trans
      (FieldSectionModules.FieldBaseChange.baseRingStructureSectionsIso (pullback.snd f (affineBaseChangeMap R K))
        (affineBaseChangedOpen K f U)).toLinearEquiv)

theorem affineBaseChangeStructureSectionsEquiv_tmul (U : X.Opens) (hU : IsAffineOpen U)
    (a : K) (x : ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)).obj.obj (op U)) :
    affineBaseChangeStructureSectionsEquiv K f U hU (a ⊗ₜ[R] x) =
      baseRingProductLeftMap f (affineBaseChangeMap R K) U ⊤ x *
        baseRingProductRightMap f (affineBaseChangeMap R K) U ⊤ ((Scheme.ΓSpecIso (.of K)).inv a) := by
  change affineBaseChangeSectionsRingEquiv K f U hU (a ⊗ₜ[R] x) = _
  exact affineBaseChangeSectionsRingEquiv_tmul K f U hU a x

theorem affineBaseChangedOpen_eq_preimage (U : X.Opens) :
    affineBaseChangedOpen K f U = (pullback.fst f (affineBaseChangeMap R K)) ⁻¹ᵁ U := by
  simp [affineBaseChangedOpen, baseRingProductRectangle]

theorem affineBaseChangedOpen_affine (U : X.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (affineBaseChangedOpen K f U) :=
  baseRingProductRectangle_affine f (affineBaseChangeMap R K) U ⊤ hU (isAffineOpen_top _)

end FieldBaseChange

/-! The canonical affine base-change comparison commutes with restriction of regular functions. -/

namespace FieldBaseChange

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorPushoutCoordinates.Construction

universe u

variable {R : Type u} (K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {U V : X.Opens} (i : V ⟶ U)

include i in
theorem affineBaseChangedOpen_mono : affineBaseChangedOpen K f V ≤ affineBaseChangedOpen K f U :=
  inf_le_inf ((pullback.fst f (affineBaseChangeMap R K)).preimage_mono i.le) le_rfl

theorem affineBaseChangeLeft_restrict :
    X.presheaf.map i.op ≫ baseRingProductLeftMap f (affineBaseChangeMap R K) V ⊤ =
      baseRingProductLeftMap f (affineBaseChangeMap R K) U ⊤ ≫
        (pullback f (affineBaseChangeMap R K)).presheaf.map
          (homOfLE (affineBaseChangedOpen_mono K f i)).op := by
  change X.presheaf.map i.op ≫ (pullback.fst f (affineBaseChangeMap R K)).appLE V _ inf_le_left =
    (pullback.fst f (affineBaseChangeMap R K)).appLE U _ inf_le_left ≫ _
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem affineBaseChangeRight_restrict :
    baseRingProductRightMap f (affineBaseChangeMap R K) V ⊤ =
      baseRingProductRightMap f (affineBaseChangeMap R K) U ⊤ ≫
        (pullback f (affineBaseChangeMap R K)).presheaf.map
          (homOfLE (affineBaseChangedOpen_mono K f i)).op := by
  change (pullback.snd f (affineBaseChangeMap R K)).appLE ⊤ _ inf_le_right =
    (pullback.snd f (affineBaseChangeMap R K)).appLE ⊤ _ inf_le_right ≫ _
  rw [Scheme.Hom.appLE_map]

theorem affineBaseChangeStructureSectionsEquiv_restrict (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (z : K ⊗[R] (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)).obj.obj (op U))) :
    affineBaseChangeStructureSectionsEquiv K f V hV
      ((((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)).obj.map i.op).hom.baseChange K z) =
      (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf (pullback.snd f (affineBaseChangeMap R K))).obj
        (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (pullback f (affineBaseChangeMap R K)))).obj.map
          (homOfLE (affineBaseChangedOpen_mono K f i)).op)
            (affineBaseChangeStructureSectionsEquiv K f U hU z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a x =>
    change FieldSectionModules.FieldBaseChange.baseRingSectionsAlgebra f U at x
    change affineBaseChangeSectionsRingEquiv K f V hV (a ⊗ₜ[R] X.presheaf.map i.op x) =
      (pullback f (affineBaseChangeMap R K)).presheaf.map
        (homOfLE (affineBaseChangedOpen_mono K f i)).op
          (affineBaseChangeSectionsRingEquiv K f U hU (a ⊗ₜ[R] x))
    rw [affineBaseChangeSectionsRingEquiv_tmul K f V hV a (X.presheaf.map i.op x),
      affineBaseChangeSectionsRingEquiv_tmul K f U hU a x]
    have hmul := ((pullback f (affineBaseChangeMap R K)).presheaf.map
      (homOfLE (affineBaseChangedOpen_mono K f i)).op).hom.map_mul
        (baseRingProductLeftMap f (affineBaseChangeMap R K) U ⊤ x)
        (baseRingProductRightMap f (affineBaseChangeMap R K) U ⊤ ((Scheme.ΓSpecIso (.of K)).inv a))
    rw [hmul]
    exact congrArg₂ (fun a b ↦ a * b)
      (congrArg (fun q : Γ(X, U) ⟶ Γ(pullback f (affineBaseChangeMap R K), affineBaseChangedOpen K f V) ↦ q x)
        (affineBaseChangeLeft_restrict K f i))
      (congrArg (fun q : Γ(Spec (.of K), ⊤) ⟶
        Γ(pullback f (affineBaseChangeMap R K), affineBaseChangedOpen K f V) ↦
          q ((Scheme.ΓSpecIso (.of K)).inv a)) (affineBaseChangeRight_restrict K f i))

end FieldBaseChange

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldAffineSections
