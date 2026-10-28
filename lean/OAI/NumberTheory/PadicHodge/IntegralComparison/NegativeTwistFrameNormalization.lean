import OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistPowerInclusion
import OAI.NumberTheory.PadicHodge.IntegralComparison.RestrictedUnitFrame

/-! # Negative Twist Frame Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistFrameNormalization

noncomputable section

/-! The standard negative-twist frame on its distinguished chart is the
restriction of the actual tensor power of the ideal inclusion. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistPowerInclusion OAI.NumberTheory.PadicHodge.IntegralComparison.RestrictedUnitFrame

universe u

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem restrict_unitTensor_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).map (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso Y).hom ≫
      (Scheme.Modules.restrictUnitIso f).hom =
    (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.restrictMonoidalTensorIso f (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)).hom ≫
      ((Scheme.Modules.restrictUnitIso f).hom ⊗ₘ (Scheme.Modules.restrictUnitIso f).hom) ≫
        (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso X).hom := by
  let F := Scheme.Modules.restrictFunctor f
  let r := Scheme.Modules.restrictUnitIso f
  let d := AlgebraicGeometry.SheafCohomology.Projective.TensorSections.restrictMonoidalTensorIso f (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)
  have he : r.symm ≪≫ F.mapIso (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso Y).symm ≪≫ d =
      (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso X).symm ≪≫ (r.symm ⊗ᵢ r.symm) := by
    apply Iso.ext
    exact AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections.poleTensor_restrict_unitObjTensorIso_inv f
  have hi := congrArg Iso.inv he
  change d.inv ≫ F.map (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso Y).hom ≫ r.hom =
    (r.hom ⊗ₘ r.hom) ≫ (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso X).hom at hi
  apply (cancel_epi d.inv).mp
  change d.inv ≫ F.map (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso Y).hom ≫ r.hom =
    d.inv ≫ d.hom ≫ (r.hom ⊗ₘ r.hom) ≫ (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso X).hom
  rw [d.inv_hom_id_assoc]
  exact hi

theorem restrict_tensorToUnit {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (g : M ⟶ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) (h : N ⟶ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) :
    (Scheme.Modules.restrictFunctor f).map ((g ⊗ₘ h) ≫ (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso Y).hom) ≫
        (Scheme.Modules.restrictUnitIso f).hom =
      (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.restrictMonoidalTensorIso f M N).hom ≫
        (((Scheme.Modules.restrictFunctor f).map g ≫ (Scheme.Modules.restrictUnitIso f).hom) ⊗ₘ
          ((Scheme.Modules.restrictFunctor f).map h ≫ (Scheme.Modules.restrictUnitIso f).hom)) ≫
        (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso X).hom := by
  let F := Scheme.Modules.restrictFunctor f
  let r := Scheme.Modules.restrictUnitIso f
  let : (Scheme.Modules.pullback f).Monoidal := AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  let : F.Monoidal := Functor.Monoidal.transport (Scheme.Modules.restrictFunctorIsoPullback f).symm
  have hn := (Functor.OplaxMonoidal.δ_natural F g h).symm
  change F.map (g ⊗ₘ h) ≫
      (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.restrictMonoidalTensorIso f (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)).hom =
    (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.restrictMonoidalTensorIso f M N).hom ≫ (F.map g ⊗ₘ F.map h) at hn
  rw [Functor.map_comp, Category.assoc, restrict_unitTensor_hom, reassoc_of% hn,
    tensorHom_comp_tensorHom_assoc]

variable {R : Type u} [CommRing R] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem base_over (j : σ) :
    (AlgebraicGeometry.SheafCohomology.Projective.IdealModule.idealModuleToUnit (AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).over (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) =
      (AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) j j).hom := by
  apply (cancel_epi (AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) j j).inv).mp
  rw [AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization_inv_comp,
    AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_self, Iso.inv_hom_id]
  let : ∀ V, IsMulCommutative ((Proj (homogeneousSubmodule σ R)).ringCatSheaf.obj.obj V) :=
    fun V => by
      change IsMulCommutative ((Proj (homogeneousSubmodule σ R)).presheaf.obj V)
      exact IsMulCommutative.of_comm fun a b => mul_comm a b
  exact (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEndRingHom
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)).map_one

theorem base_restriction (j : σ) :
    (Scheme.Modules.restrictFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j).ι).map
        (AlgebraicGeometry.SheafCohomology.Projective.IdealModule.idealModuleToUnit (AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)) ≫
      (Scheme.Modules.restrictUnitIso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j).ι).hom =
    (AlgebraicGeometry.SheafCohomology.Projective.HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) j j).inv :=
  RestrictedUnitFrame.restriction_eq_of_over_eq (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) _
    (AlgebraicGeometry.SheafCohomology.Projective.HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) j j).symm (base_over j)

theorem inclusion_restriction (j : σ) (n : ℕ) :
    (Scheme.Modules.restrictFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j).ι).map (NegativeTwistPowerInclusion.inclusion (R := R) j n) ≫
        (Scheme.Modules.restrictUnitIso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j).ι).hom =
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization (R := R) j j n).hom := by
  induction n with
  | zero =>
    exact AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections.poleTensor_restrict_monoidalUnitObjIso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j).ι
  | succ n ih =>
    change (Scheme.Modules.restrictFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j).ι).map
      ((NegativeTwistPowerInclusion.inclusion (R := R) j n ⊗ₘ AlgebraicGeometry.SheafCohomology.Projective.IdealModule.idealModuleToUnit (AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)) ≫
        (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso _).hom) ≫ (Scheme.Modules.restrictUnitIso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j).ι).hom = _
    rw [restrict_tensorToUnit, ih, base_restriction]
    rfl

theorem inclusion_over (j : σ) (n : ℕ) :
    (NegativeTwistPowerInclusion.inclusion (R := R) j n).over (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) =
      (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j n).hom :=
  RestrictedUnitFrame.over_eq_of_restriction_eq (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) _
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization (R := R) j j n)
    (inclusion_restriction j n)

theorem coefficient_eq_frame (j : σ) (n : ℕ)
    (x : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) :
    AlgebraicGeometry.SheafCohomology.Projective.NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j n x =
      (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
        (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j n)).symm x := by
  have h := congrArg (fun f => f.val.app (op (Over.mk (𝟙 (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)))))
    (inclusion_over (R := R) j n)
  exact (NegativeTwistPowerInclusion.inclusion_eq_coefficient j n x).symm.trans (ConcreteCategory.congr_hom h x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistFrameNormalization
