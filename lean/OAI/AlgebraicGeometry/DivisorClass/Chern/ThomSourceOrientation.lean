import OAI.AlgebraicGeometry.DivisorClass.Chern.ThomOrientationSheaf
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SheafZeroIso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafPullback

/-! # Thom Source Orientation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ThomSourceOrientation

noncomputable section

section

/-!
# ChernClass: the original Thom orientation is the actual source resolution's degree zero

The comparison uses point evaluation in source singular cochains and the
original normalized Thom germs. In degree zero a left exact functor
preserves cohomology because there are no incoming boundaries. Thus the
genuine pushforward sheaf complex has exactly the required source sheaf.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def cochainLeftExactZeroHomologyIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (K : CochainComplex C ℕ) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology 0 ≅
      F.obj (K.homology 0) :=
  (CochainComplex.isoHomologyπ₀ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).symm ≪≫
    AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactCyclesIso (K.sc 0) F ≪≫ F.mapIso K.isoHomologyπ₀

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

def regularThomSourceOrientationIso :
    Z.regularThomSheafComplex.homology (2 * p) ≅
      (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) Z.regularComplementTopCatMap).homology 0 := by
  let := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace
    Z.regularAnalyticModel (TopCat.of Z.regularAnalyticSpace)
  exact ThomOrientationSheaf.regularThomOrientationSheafIso Z ≪≫
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) Z.regularComplementTopCatMap).mapIso
      (Rational.SheafZeroIso.RationalCech.locallyConstantRationalSheafZeroIso (TopCat.of Z.regularAnalyticSpace)) ≪≫
    (cochainLeftExactZeroHomologyIso
      (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex
        (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)))
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) Z.regularComplementTopCatMap)).symm

end

/-! The source-orientation comparison uses the literal degree-zero augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
variable (K : CochainComplex C ℕ) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

theorem cochainLeftExactZeroHomologyIso_hom_eq :
    (cochainLeftExactZeroHomologyIso K F).hom = AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison (K.sc 0) F := by
  apply (cancel_epi (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ 0)).mp
  calc
    _ = (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactCyclesIso (K.sc 0) F).hom ≫ F.map (K.homologyπ 0) := by
      change (CochainComplex.isoHomologyπ₀
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).hom ≫
          (cochainLeftExactZeroHomologyIso K F).hom = _
      simp only [cochainLeftExactZeroHomologyIso, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, Iso.hom_inv_id_assoc]
      rfl
    _ = _ := (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.homologyπ_leftExactHomologyComparison (K.sc 0) F).symm

theorem cochainLeftExactZeroHomologyIso_inclusion :
    (cochainLeftExactZeroHomologyIso K F).hom ≫ F.map (K.isoHomologyπ₀.inv ≫ K.iCycles 0) =
      (CochainComplex.isoHomologyπ₀ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).inv ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles 0 := by
  have hF : F.map K.isoHomologyπ₀.hom ≫ F.map (K.isoHomologyπ₀.inv ≫ K.iCycles 0) =
      F.map (K.iCycles 0) := by
    rw [← F.map_comp, Iso.hom_inv_id_assoc]
  simp only [cochainLeftExactZeroHomologyIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [hF]
  exact congrArg (fun g => (CochainComplex.isoHomologyπ₀
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).inv ≫ g)
    (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactCyclesIso_hom_iCycles (K.sc 0) F)

namespace RationalCech

variable (X : TopCat.{0}) [LocallyPathConnectedSpace X]

theorem locallyConstantRationalPresheafZeroIso_inclusion :
    (Rational.SheafZeroIso.RationalCech.locallyConstantRationalPresheafZeroIso X).hom ≫
      (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).isoHomologyπ₀.inv ≫
        (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).iCycles 0 =
      Cech.Obj.RationalCech.locallyConstantSingularAugmentation X := by
  rw [Rational.SheafZeroIso.RationalCech.locallyConstantRationalPresheafZeroIso, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

theorem locallyConstantRationalSheafZeroIso_inclusion :
    (Rational.SheafZeroIso.RationalCech.locallyConstantRationalSheafZeroIso X).hom ≫
      (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)).isoHomologyπ₀.inv ≫
        (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)).iCycles 0 =
    (sheafificationIso (Rational.ConstantSheaf.RationalCech.locallyConstantRationalSheaf X)).hom ≫
      (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).map
        (Cech.Obj.RationalCech.locallyConstantSingularAugmentation X) := by
  let K := AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X
  let F := presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)
  have hc := cochainLeftExactZeroHomologyIso_inclusion K F
  rw [cochainLeftExactZeroHomologyIso_hom_eq,
    AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition.leftExactHomologyComparison_eq_mapHomologyIso] at hc
  have hi : ((K.sc 0).mapHomologyIso F).inv ≫
      (CochainComplex.isoHomologyπ₀ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).inv ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles 0 =
      F.map (K.isoHomologyπ₀.inv ≫ K.iCycles 0) :=
    ((K.sc 0).mapHomologyIso F).inv_comp_eq.mpr hc.symm
  unfold Rational.SheafZeroIso.RationalCech.locallyConstantRationalSheafZeroIso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  change (sheafificationIso (Rational.ConstantSheaf.RationalCech.locallyConstantRationalSheaf X)).hom ≫
    F.map (Rational.SheafZeroIso.RationalCech.locallyConstantRationalPresheafZeroIso X).hom ≫
      ((K.sc 0).mapHomologyIso F).inv ≫
        (CochainComplex.isoHomologyπ₀ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).inv ≫
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles 0 = _
  rw [hi, ← F.map_comp]
  exact congrArg (fun g => (sheafificationIso (Rational.ConstantSheaf.RationalCech.locallyConstantRationalSheaf X)).hom ≫ F.map g)
    (locallyConstantRationalPresheafZeroIso_inclusion X)

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ThomSourceOrientation
