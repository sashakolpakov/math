import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.UnitEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.HomUnitEvaluation

/-! # Unit Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.UnitMap

noncomputable section

/-! The original common-refinement dual of the coefficient unit is
literal evaluation at one under the actual globally glued adjunction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomGlobal

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) {Y : Scheme.{u}}
  (f : Y ⟶ X.left) [IsFinite f] [Flat f]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R n) [IsClosedImmersion i.left]
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n)

def unit : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (Projective.IntrinsicOverlap.Intrinsic.space R n) ⟶ HomLocal.coefficient X f i :=
  SheafOfModules.unitToPushforwardObjUnit i.left.toRingCatSheafHom ≫
    Cech.StructurePullbackUnit.sheafMap f i.left

def evaluation : HomLocal.targetSheaf X f i g ⟶ HomLocal.formSheaf X i g :=
  Sheaf.HomUnitEvaluation.map (HomLocal.coefficient X f i) (HomLocal.formSheaf X i g) (unit X f i)

omit [IsNoetherianRing R] [IsFinite f] [Flat f] [IsClosedImmersion (Over.Hom.left i)] [IsProper X.hom] in
theorem unit_one (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) :
    (unit X f i).app U (1 : Γ(Projective.IntrinsicOverlap.Intrinsic.space R n, U)) =
      (show Γ(HomLocal.coefficient X f i, U) from (1 : Γ(Y, f ⁻¹ᵁ (i.left ⁻¹ᵁ U)))) := by
  change (f.app (i.left ⁻¹ᵁ U)).hom ((i.left.app U).hom 1) = 1
  simp only [map_one]

theorem normalization :
    (HomGlobal.iso X f i g j B hB hg).hom ≫ evaluation X f i g =
      UnitEvaluation.dualUnit X f i g j B hB ≫
        (HomLocal.scalarAdjunction X i g j B hB hg).hom := by
  apply AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BasisIsomorphisms.moduleMap_eq_of_basis
    (Principal.BasisGluing.opens HomGlobal.Good)
    (Principal.BasisGluing.isBasis HomGlobal.Good HomGlobal.exists_neighborhood)
  intro U
  apply ConcreteCategory.hom_ext
  intro z
  have he := congrArg₂ (fun (q : Γ(HomLocal.targetSheaf X f i g, U.val))
      (m : Γ(HomLocal.coefficient X f i, U.val)) =>
        ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (HomLocal.coefficient X f i) (HomLocal.formSheaf X i g) U.val q m)
    (HomGlobal.iso_app X f i g j B hB hg U.val U.property.1 U.property.2 z)
    (unit_one X f i U.val)
  exact he.trans (UnitEvaluation.evaluation X f i g j B hB hg
    U.val U.property.1 U.property.2.choose U.property.2.choose_spec z)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.UnitMap
