import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.Winding
import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingLoop
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity
import OAI.AlgebraicTopology.Cohomology.Singular.Contractible

/-! # Normal Winding -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.NormalWinding

noncomputable section

/-!
# ChernClass: compare actual winding with the existing normal-coordinate group

The positive-loop-normalized singular winding gives a nonzero relative class
on the actual normal complex line. Its coefficient in the existing geometric
normalization is defined by the genuine relative-cohomology coordinate map
and proved nonzero. Determining its sign requires comparing the geometric
Mayer–Vietoris orientation with the positive-loop normalization.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular.Contractible OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

abbrev windingNormalLine : TopCat.{0} := TopCat.of (Fin 1 → ℂ)
abbrev windingNormalPunctured : Set windingNormalLine := {0}ᶜ

/-- The actual complex coordinate on the punctured normal line. -/
def normalPuncturedCoordinate : C(windingNormalPunctured, ℂ) :=
  ⟨fun x => x.val 0, (continuous_apply 0).comp continuous_subtype_val⟩

theorem normalPuncturedCoordinate_ne_zero (x : windingNormalPunctured) : normalPuncturedCoordinate x ≠ 0 := by
  intro hx
  apply x.property
  change x.val = 0
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hx

/-- The actual one-coordinate identification with the punctured plane. -/
def normalPuncturedHomeomorph : TopCat.of windingNormalPunctured ≃ₜ WindingLoop.puncturedPlane where
  toFun x := ⟨normalPuncturedCoordinate x, normalPuncturedCoordinate_ne_zero x⟩
  invFun z := ⟨fun _ => z.val, by
    intro hz
    apply z.property
    exact congrFun hz 0⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.val (Subsingleton.elim 0 i)
  right_inv _ := rfl
  continuous_toFun := normalPuncturedCoordinate.continuous.subtype_mk _
  continuous_invFun := (continuous_pi (fun _ => continuous_subtype_val)).subtype_mk (fun z => by
    intro hz
    exact z.property (congrFun hz 0))

/-- The coordinate winding remains nonzero in the project's actual normal-line model. -/
theorem normalCoordinateWinding_ne_zero :
    WindingSingular.singularWindingClass (TopCat.of windingNormalPunctured) normalPuncturedCoordinate
      normalPuncturedCoordinate_ne_zero ≠ 0 := by
  intro hz
  have h := WindingSingular.singularWindingClass_naturality (TopCat.isoOfHomeo normalPuncturedHomeomorph).inv
    normalPuncturedCoordinate normalPuncturedCoordinate_ne_zero
  change AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (TopCat.isoOfHomeo normalPuncturedHomeomorph).inv 1
      (WindingSingular.singularWindingClass (TopCat.of windingNormalPunctured) normalPuncturedCoordinate
        normalPuncturedCoordinate_ne_zero) =
    WindingSingular.singularWindingClass WindingLoop.puncturedPlane WindingLoop.puncturedCoordinate WindingLoop.puncturedCoordinate_ne_zero at h
  rw [hz, map_zero] at h
  exact WindingLoop.singularWindingClass_punctured_ne_zero h.symm

/-- The actual connecting isomorphism of the contractible normal line. -/
def normalWindingConnectingIso :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of windingNormalPunctured) 1 ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) windingNormalLine windingNormalPunctured 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnectingIso (ModuleCat.of ℚ ℚ) windingNormalLine windingNormalPunctured 1
    (AlgebraicTopology.Cohomology.Singular.Contractible.isZero_singularCohomology_of_contractible _ _ 1 (by decide))
    (AlgebraicTopology.Cohomology.Singular.Contractible.isZero_singularCohomology_of_contractible _ _ 2 (by decide))

/-- The relative class normalized by actual positive logarithm winding. -/
def normalSupportedWindingClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) windingNormalLine windingNormalPunctured 2 :=
  Supported.Winding.supportedWindingClass windingNormalLine windingNormalPunctured normalPuncturedCoordinate
    normalPuncturedCoordinate_ne_zero

theorem normalSupportedWindingClass_ne_zero : normalSupportedWindingClass ≠ 0 := by
  intro hz
  apply normalCoordinateWinding_ne_zero
  apply normalWindingConnectingIso.toLinearEquiv.injective
  change normalSupportedWindingClass = normalWindingConnectingIso.hom 0
  rw [hz, map_zero]

/-- The exact comparison coefficient in the independently constructed geometric normal group. -/
def normalWindingCoefficient : ℚ :=
  CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyEquiv 1 normalSupportedWindingClass

theorem normalWindingCoefficient_ne_zero : normalWindingCoefficient ≠ 0 := by
  intro hz
  apply normalSupportedWindingClass_ne_zero
  apply (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyEquiv 1).injective
  change normalWindingCoefficient = (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyEquiv 1) 0
  rw [hz, map_zero]

/-- An unconditional comparison of the two actual classes, retaining the
normalization coefficient which still needs its orientation calculation. -/
theorem normalSupportedWindingClass_eq_coefficient_smul :
    normalSupportedWindingClass = normalWindingCoefficient • CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1 := by
  apply (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyEquiv 1).injective
  rw [map_smul, CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass_normalization]
  change normalWindingCoefficient = normalWindingCoefficient * 1
  exact (mul_one _).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.NormalWinding
