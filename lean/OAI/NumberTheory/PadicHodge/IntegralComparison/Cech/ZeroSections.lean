import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Augmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopCechRightExact

/-! # Zero Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ZeroSections

noncomputable section

/-! Degree-zero cohomology of the actual ordered Čech complex is the
module of global sections. The comparison uses the global restriction
map, so it preserves the unit and is natural in the coefficient sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Scheme.Modules OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Augmentation

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)

def lift (M : X.Modules) : (OrderedCech.Augmentation.sections π).obj M ⟶ (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).cycles 0 :=
  (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).liftCycles (OrderedCech.Augmentation.map π U M) 1 (by simp) (OrderedCech.Augmentation.map_d π U M hU)

@[reassoc (attr := simp)]
theorem lift_i (M : X.Modules) :
    lift π U hU M ≫ (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).iCycles 0 = OrderedCech.Augmentation.map π U M :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

theorem lift_bijective (M : X.Modules) : Function.Bijective (lift π U hU M) := by
  let K := AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U
  have hm : Function.Injective (OrderedCech.Augmentation.map π U M) :=
    (ModuleCat.mono_iff_injective _).mp (OrderedCech.Augmentation.map_mono π U M hU)
  have hi : Function.Injective (K.iCycles 0) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  constructor
  · intro x y hxy
    apply hm
    have hx := ConcreteCategory.congr_hom (lift_i π U hU M) x
    have hy := ConcreteCategory.congr_hom (lift_i π U hU M) y
    exact hx.symm.trans ((congrArg (K.iCycles 0) hxy).trans hy)
  · intro z
    have hz : K.d 0 1 (K.iCycles 0 z) = 0 := by
      have h := ConcreteCategory.congr_hom (K.iCycles_d 0 1) z
      exact h
    let e := AlgebraicGeometry.SheafCohomology.Projective.ZeroCyclesLinearSections.orderedBaseTopSectionsZeroCyclesLinearEquiv π M U hU
    refine ⟨e.symm ⟨K.iCycles 0 z, hz⟩, hi ?_⟩
    rw [← ConcreteCategory.comp_apply, lift_i]
    exact (OrderedCech.Augmentation.map_eq_zeroCycle π U M hU _).trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨K.iCycles 0 z, hz⟩))

instance lift_isIso (M : X.Modules) : IsIso (lift π U hU M) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (lift_bijective π U hU M)

def iso (M : X.Modules) :
    (OrderedCech.Augmentation.sections π).obj M ≅ (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology 0 :=
  asIso (lift π U hU M) ≪≫ (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).isoHomologyπ₀

@[simp]
theorem iso_hom (M : X.Modules) :
    (iso π U hU M).hom = lift π U hU M ≫ (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homologyπ 0 := rfl

@[reassoc]
theorem lift_naturality {M N : X.Modules} (f : M ⟶ N) :
    (OrderedCech.Augmentation.sections π).map f ≫ lift π U hU N =
      lift π U hU M ≫ HomologicalComplex.cyclesMap ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map f) 0 := by
  let a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U ⟶ AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U :=
    (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map f
  have ha : HomologicalComplex.cyclesMap a 0 ≫ (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U).iCycles 0 =
      (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).iCycles 0 ≫ a.f 0 :=
    HomologicalComplex.cyclesMap_i a 0
  apply (cancel_mono ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U).iCycles 0)).mp
  change ((OrderedCech.Augmentation.sections π).map f ≫ lift π U hU N) ≫ (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U).iCycles 0 =
    (lift π U hU M ≫ HomologicalComplex.cyclesMap a 0) ≫ (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U).iCycles 0
  rw [Category.assoc, lift_i, Category.assoc, ha, lift_i_assoc]
  exact OrderedCech.Augmentation.naturality π U f

@[reassoc]
theorem naturality {M N : X.Modules} (f : M ⟶ N) :
    (OrderedCech.Augmentation.sections π).map f ≫ (iso π U hU N).hom =
      (iso π U hU M).hom ≫
        HomologicalComplex.homologyMap ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map f) 0 := by
  let a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U ⟶ AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U :=
    (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map f
  have ha : HomologicalComplex.cyclesMap a 0 ≫ (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U).homologyπ 0 =
      (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homologyπ 0 ≫ HomologicalComplex.homologyMap a 0 :=
    (HomologicalComplex.homologyπ_naturality a 0).symm
  simp only [iso_hom, ← Category.assoc]
  rw [lift_naturality, Category.assoc]
  change lift π U hU M ≫ (HomologicalComplex.cyclesMap a 0 ≫
      (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U).homologyπ 0) = _
  rw [ha]
  simp only [Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ZeroSections
