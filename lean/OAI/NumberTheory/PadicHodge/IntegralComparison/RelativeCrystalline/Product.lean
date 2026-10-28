import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamAdditiveProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamWedgeAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechProduct

/-! # Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Product

noncomputable section

/-! The actual relative crystalline form presheaves carry the native PD
product. Their coefficient-ring augmentation preserves multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)

local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex.complex H Q π

def sectionPairing (a b : ℕ) (U : Cᵒᵖ) :
    ((P).X a).obj U →ₗ[B] ((P).X b).obj U →ₗ[B] ((P).X (a + b)).obj U := by
  letI : Algebra (Q.obj U.unop).ring (H.obj U.unop).ring := FormData.relativeAlgebra H Q π U.unop
  let μ := (PD.DeRhamWedge.wedge (Q.obj U.unop).ring (H.obj U.unop).ring
    (H.obj U.unop).ideal (H.obj U.unop).dividedPowers a b).restrictScalars₁₂
      (Q.obj U.unop).ring (Q.obj U.unop).ring
  exact LinearMap.mk₂ B (fun x y => μ x y)
    (fun x x' y => DFunLike.congr_fun (μ.map_add x x') y)
    (fun b x y => DFunLike.congr_fun (μ.map_smul ((Q.obj U.unop).base b) x) y)
    (fun x y y' => (μ x).map_add y y')
    (fun b x y => (μ x).map_smul ((Q.obj U.unop).base b) y)

theorem sectionPairing_natural (a b : ℕ) {U V : Cᵒᵖ} (α : U ⟶ V)
    (x : ((P).X a).obj U) (y : ((P).X b).obj U) :
    ((P).X (a + b)).map α (sectionPairing H Q π a b U x y) =
      sectionPairing H Q π a b V (((P).X a).map α x) (((P).X b).map α y) := by
  let : Algebra (Q.obj U.unop).ring (H.obj U.unop).ring := FormData.relativeAlgebra H Q π U.unop
  let : Algebra (Q.obj V.unop).ring (H.obj V.unop).ring := FormData.relativeAlgebra H Q π V.unop
  exact PD.DeRhamAdditiveProduct.Wedge.addMap_wedge (Q.obj U.unop).ring (Q.obj V.unop).ring
    (H.obj U.unop).ring (H.obj V.unop).ring
    (H.obj U.unop).ideal (H.obj U.unop).dividedPowers
    (H.obj V.unop).ideal (H.obj V.unop).dividedPowers
    (H.map α.unop).ringMap.toRingHom (fun n => FormData.formsMap H Q π α.unop n)
    (fun n c t => FormMaps.formsMap_symbol H Q π α.unop n c t)
    a b x y

theorem sectionDegreeCast_apply {a b : ℕ} (e : a = b) (U : Cᵒᵖ) (x : ((P).X a).obj U) :
    letI : Algebra (Q.obj U.unop).ring (H.obj U.unop).ring := FormData.relativeAlgebra H Q π U.unop
    Presheaf.CechProduct.sectionDegreeCast P e U x =
      PD.DeRhamLeibniz.Wedge.degreeCast (Q.obj U.unop).ring (H.obj U.unop).ring
        (H.obj U.unop).ideal (H.obj U.unop).dividedPowers e x := by
  subst b
  rfl

theorem sectionPairing_differential (a b : ℕ) (U : Cᵒᵖ)
    (x : ((P).X a).obj U) (y : ((P).X b).obj U) :
    ((P).d (a + b) (a + b + 1)).app U (sectionPairing H Q π a b U x y) =
      Presheaf.CechProduct.sectionDegreeCast P (by omega : (a + 1) + b = a + b + 1) U
        (sectionPairing H Q π (a + 1) b U (((P).d a (a + 1)).app U x) y) +
      (-1 : ℤ) ^ a • Presheaf.CechProduct.sectionDegreeCast P
        (by omega : a + (b + 1) = a + b + 1) U
        (sectionPairing H Q π a (b + 1) U x (((P).d b (b + 1)).app U y)) := by
  let : Algebra (Q.obj U.unop).ring (H.obj U.unop).ring := FormData.relativeAlgebra H Q π U.unop
  rw [sectionDegreeCast_apply, sectionDegreeCast_apply]
  rw [ModuleComplex.complex_d,
    ModuleComplex.complex_d,
    ModuleComplex.complex_d]
  exact PD.DeRhamLeibniz.Wedge.differential_wedge (Q.obj U.unop).ring (H.obj U.unop).ring
    (H.obj U.unop).ideal (H.obj U.unop).dividedPowers a b x y

def unitSection (U : Cᵒᵖ) : ((P).X 0).obj U := by
  let : Algebra (Q.obj U.unop).ring (H.obj U.unop).ring := FormData.relativeAlgebra H Q π U.unop
  exact PD.DeRhamWedgeAlgebra.unitForm (Q.obj U.unop).ring (H.obj U.unop).ring
    (H.obj U.unop).ideal (H.obj U.unop).dividedPowers

theorem augmentationZero_mul (U : Cᵒᵖ) (a b : (Q.obj U.unop).ring) :
    (ModuleComplex.augmentationZero H Q π).app U (a * b) =
      sectionPairing H Q π 0 0 U
        ((ModuleComplex.augmentationZero H Q π).app U a)
        ((ModuleComplex.augmentationZero H Q π).app U b) := by
  let : Algebra (Q.obj U.unop).ring (H.obj U.unop).ring := FormData.relativeAlgebra H Q π U.unop
  change Augmentation.constants H Q π U.unop (a * b) =
    PD.DeRhamWedge.wedge (Q.obj U.unop).ring (H.obj U.unop).ring
      (H.obj U.unop).ideal (H.obj U.unop).dividedPowers 0 0
      (Augmentation.constants H Q π U.unop a)
      (Augmentation.constants H Q π U.unop b)
  rw [Augmentation.constants_symbol,
    Augmentation.constants_symbol,
    Augmentation.constants_symbol]
  change AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol _ _ _ _ _ _ = PD.DeRhamWedge.wedge _ _ _ _ 0 0
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol _ _ _ _ _ _) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol _ _ _ _ _ _)
  rw [PD.DeRhamWedge.wedge_symbol,
    show (π.app U.unop).ringMap (a * b) =
      (π.app U.unop).ringMap a * (π.app U.unop).ringMap b from
        (π.app U.unop).ringMap.toRingHom.map_mul a b]
  apply congrArg (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol (Q.obj U.unop).ring (H.obj U.unop).ring
    (H.obj U.unop).ideal (H.obj U.unop).dividedPowers
    ((π.app U.unop).ringMap a * (π.app U.unop).ringMap b))
  funext i
  exact i.elim0

theorem augmentationZero_unit (U : Cᵒᵖ) :
    (ModuleComplex.augmentationZero H Q π).app U
        (1 : (Q.obj U.unop).ring) =
      unitSection H Q π U := by
  let : Algebra (Q.obj U.unop).ring (H.obj U.unop).ring := FormData.relativeAlgebra H Q π U.unop
  change Augmentation.constants H Q π U.unop 1 = _
  rw [Augmentation.constants_symbol,
    show (π.app U.unop).ringMap 1 = 1 from (π.app U.unop).ringMap.toRingHom.map_one]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Product
