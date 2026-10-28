import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeSectionsAsAlgebra
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeTensorPushoutCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Cube Product Sections -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSections.Construction.CubeCech

noncomputable section

/-! Tensor-product coordinates for regular functions on affine rectangles in a product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))

abbrev productRectangle (U : X.Opens) (V : Y.Opens) : (pullback f g).Opens :=
  (pullback.fst f g) ⁻¹ᵁ U ⊓ (pullback.snd f g) ⁻¹ᵁ V

abbrev productRectangleLeftMap (U : X.Opens) (V : Y.Opens) :
    Γ(X, U) ⟶ Γ(pullback f g, productRectangle f g U V) :=
  (pullback.fst f g).appLE U _ inf_le_left

abbrev productRectangleRightMap (U : X.Opens) (V : Y.Opens) :
    Γ(Y, V) ⟶ Γ(pullback f g, productRectangle f g U V) :=
  (pullback.snd f g).appLE V _ inf_le_right

theorem productRectangleSections_isPushout (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsPushout (CommRingCat.ofHom (algebraMap k (CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra f U)))
      (CommRingCat.ofHom (algebraMap k (CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra g V)))
      (productRectangleLeftMap f g U V) (productRectangleRightMap f g U V) := by
  let H := IsPullback.of_hasPullback f g
  have hp := (isIso_pushoutSection_iff H (show V ≤ g ⁻¹ᵁ ⊤ by simp)
    (show U ≤ f ⁻¹ᵁ ⊤ by simp) (rfl : productRectangle f g U V = _)).mp
      (isIso_pushoutSection_of_isAffineOpen H (show V ≤ g ⁻¹ᵁ ⊤ by simp)
        (show U ≤ f ⁻¹ᵁ ⊤ by simp) rfl
        (isAffineOpen_top (Spec (.of k))) hV hU)
  refine hp.of_iso (Scheme.ΓSpecIso (.of k)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by exact (Category.comp_id _).trans (Category.id_comp _).symm)
    (by exact (Category.comp_id _).trans (Category.id_comp _).symm)
  · change f.appLE ⊤ U _ ≫ 𝟙 _ = (Scheme.ΓSpecIso (.of k)).hom ≫
      CommRingCat.ofHom (CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants f U)
    rw [CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants_eq_appLE]
    simp
  · change g.appLE ⊤ V _ ≫ 𝟙 _ = (Scheme.ΓSpecIso (.of k)).hom ≫
      CommRingCat.ofHom (CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants g V)
    rw [CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants_eq_appLE]
    simp

def productRectangleSectionsEquiv (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra f U ⊗[k] CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra g V ≃+*
      Γ(pullback f g, productRectangle f g U V) :=
  CubeTensorPushoutCoordinates.Construction.CubeCech.tensorPushoutRingEquiv _ _ _ _ _ (productRectangleSections_isPushout f g U V hU hV)

theorem productRectangleSectionsEquiv_tmul (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (x : CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra f U) (y : CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra g V) :
    productRectangleSectionsEquiv f g U V hU hV (x ⊗ₜ[k] y) =
      productRectangleLeftMap f g U V x * productRectangleRightMap f g U V y :=
  CubeTensorPushoutCoordinates.Construction.CubeCech.tensorPushoutRingEquiv_tmul _ _ _ _ _ _ x y

def productRectangleSectionsAlgEquiv (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra f U ⊗[k] CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra g V ≃ₐ[k]
      CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra (pullback.fst f g ≫ f) (productRectangle f g U V) where
  __ := productRectangleSectionsEquiv f g U V hU hV
  commutes' r := by
    change productRectangleSectionsEquiv f g U V hU hV
      (algebraMap k (CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra f U ⊗[k] CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra g V) r) =
        CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants (pullback.fst f g ≫ f) (productRectangle f g U V) r
    rw [Algebra.TensorProduct.algebraMap_apply, productRectangleSectionsEquiv_tmul]
    change productRectangleLeftMap f g U V (CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants f U r) *
      productRectangleRightMap f g U V 1 = CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants (pullback.fst f g ≫ f) _ r
    rw [map_one, mul_one]
    exact RingHom.congr_fun (CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants_pullback f (pullback.fst f g) U
      (productRectangle f g U V) inf_le_left) r

def productRectangleModuleSectionsEquiv (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U) ⊗[k]
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op V) ≃ₗ[k]
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
        (op (productRectangle f g U V)) :=
  (TensorProduct.congr (CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseModuleIso f U).toLinearEquiv
    (CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseModuleIso g V).toLinearEquiv).symm.trans
      ((productRectangleSectionsAlgEquiv f g U V hU hV).toLinearEquiv.trans
        (CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseModuleIso (pullback.fst f g ≫ f) (productRectangle f g U V)).toLinearEquiv)

theorem productRectangleModuleSectionsEquiv_tmul (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (x : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U))
    (y : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op V)) :
    productRectangleModuleSectionsEquiv f g U V hU hV (x ⊗ₜ[k] y) =
      productRectangleLeftMap f g U V x * productRectangleRightMap f g U V y := by
  change productRectangleSectionsEquiv f g U V hU hV (x ⊗ₜ[k] y) = _
  exact productRectangleSectionsEquiv_tmul f g U V hU hV x y

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSections.Construction.CubeCech
