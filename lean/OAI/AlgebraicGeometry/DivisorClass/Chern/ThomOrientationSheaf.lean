import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.SheafOrientationCoefficients
import OAI.AlgebraicGeometry.DivisorClass.Chern.ThomOrientationCoefficients
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ConstantSheaf
import OAI.AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace

/-! # Thom Orientation Sheaf -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ThomOrientationSheaf

noncomputable section

/-!
# ChernClass: the original Thom orientation sheaf on the full regular support

The actual cohomology sheaf of supported singular cochains is identified,
on every ambient open set, with locally constant rational functions on
its inverse image in the original regular support. The maps preserve all
restrictions and send the original Thom section to the constant one.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

def regularThomOrientationPresheafIso :
    (Z.regularThomSheafComplex.homology (2 * p)).obj ≅
      Open.SheafOrientationCoefficients.supportLocallyConstantPresheaf Z.regularComplementTopCatMap :=
  Open.SheafOrientationCoefficients.orientationCoefficientsPresheafIso (Z.regularThomSheafComplex.homology (2 * p))
    Z.regularComplementTopCatMap (ThomOrientationCoefficients.regularThomOrientationStalkIso Z)
    (Z.regularThomFirstCohomologyIso.hom Z.regularThomClass)
    (ThomOrientationCoefficients.regularThomOrientationSection_normalization Z)
    Z.isClosedEmbedding_regularComplementInclusion (ThomOrientationCoefficients.regularThomOrientationStalk_zero Z)

def regularThomCoefficientSheaf : TopCat.Sheaf (ModuleCat.{0} ℚ)
    (TopCat.of Z.regularAmbientSpace) :=
  (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) Z.regularComplementTopCatMap).obj
    (Rational.ConstantSheaf.RationalCech.locallyConstantRationalSheaf (TopCat.of Z.regularAnalyticSpace))

def regularThomOrientationSheafIso :
    Z.regularThomSheafComplex.homology (2 * p) ≅ regularThomCoefficientSheaf Z where
  hom := ⟨(regularThomOrientationPresheafIso Z).hom⟩
  inv := ⟨(regularThomOrientationPresheafIso Z).inv⟩
  hom_inv_id := by
    apply Sheaf.hom_ext
    exact (regularThomOrientationPresheafIso Z).hom_inv_id
  inv_hom_id := by
    apply Sheaf.hom_ext
    exact (regularThomOrientationPresheafIso Z).inv_hom_id

theorem regularThomOrientationSheafIso_apply
    (U : Opens Z.regularAmbientSpace)
    (s : (Z.regularThomSheafComplex.homology (2 * p)).obj.obj (op U))
    (x : (Opens.map Z.regularComplementTopCatMap).obj U) :
    LocallyConstant.toFun ((regularThomOrientationSheafIso Z).hom.hom.app (op U) s :
      LocallyConstant ((Opens.map Z.regularComplementTopCatMap).obj U) ℚ) x =
      (ThomOrientationCoefficients.regularThomOrientationStalkIso Z x.val).hom
        ((Z.regularThomSheafComplex.homology (2 * p)).presheaf.germ U
          (Z.regularComplementInclusion x.val) x.property s) := rfl

theorem regularThomOrientationSheafIso_thom
    (U : Opens Z.regularAmbientSpace) :
    (regularThomOrientationSheafIso Z).hom.hom.app (op U)
      ((Z.regularThomSheafComplex.homology (2 * p)).obj.map
        (homOfLE (le_top : U ≤ ⊤)).op
        (Z.regularThomFirstCohomologyIso.hom Z.regularThomClass)) =
      (1 : LocallyConstant ((Opens.map Z.regularComplementTopCatMap).obj U) ℚ) := by
  apply LocallyConstant.ext
  intro x
  exact (regularThomOrientationSheafIso_apply Z U _ x).trans
    ((congrArg (ThomOrientationCoefficients.regularThomOrientationStalkIso Z x.val).hom
      (TopCat.Presheaf.germ_res_apply
        (Z.regularThomSheafComplex.homology (2 * p)).presheaf
        (homOfLE (le_top : U ≤ ⊤)) (Z.regularComplementInclusion x.val) x.property
        (Z.regularThomFirstCohomologyIso.hom Z.regularThomClass))).trans
      (Z.regularThomClass_normalization x.val))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ThomOrientationSheaf
