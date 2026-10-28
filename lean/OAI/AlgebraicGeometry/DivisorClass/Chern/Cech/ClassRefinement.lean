import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.CechTotalRefinement
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.DegreeOneBoundary

/-! # Class Refinement -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ClassRefinement

noncomputable section

section

/-! Refinement preserves the unchanged native Cech-to-sheaf cohomology map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I J : Type} (U : I → Opens X) (V : J → Opens X)
  (r : J → I) (hr : ∀ j, V j ≤ U (r j))
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤)
  {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}
  (hK : ∀ q, IsFlasque (K.X q))

theorem nativeFlasqueCechHomologyIso_refinement (n : ℕ) :
    HomologicalComplex.homologyMap (Intrinsic.CechTotalRefinement.nativeCechTotalRefinement U V r hr K) (n + 1) ≫
      (FlasqueCechD.abelianFlasqueCechHomologyIso V K hK hV n).inv =
      (FlasqueCechD.abelianFlasqueCechHomologyIso U K hK hU n).inv := by
  let eU := FlasqueCechD.abelianFlasqueCechHomologyIso U K hK hU n
  let eV := FlasqueCechD.abelianFlasqueCechHomologyIso V K hK hV n
  have hh : eU.hom ≫ HomologicalComplex.homologyMap
      (Intrinsic.CechTotalRefinement.nativeCechTotalRefinement U V r hr K) (n + 1) = eV.hom := by
    change HomologicalComplex.homologyMap (FlasqueCechD.abelianCechHorizontalEdge U K) (n + 1) ≫ _ = _
    rw [← HomologicalComplex.homologyMap_comp, Intrinsic.CechTotalRefinement.nativeCechHorizontalEdge_refinement]
    rfl
  apply (cancel_mono eV.hom).mp
  change (HomologicalComplex.homologyMap (Intrinsic.CechTotalRefinement.nativeCechTotalRefinement U V r hr K) (n + 1) ≫
    eV.inv) ≫ eV.hom = eU.inv ≫ eV.hom
  rw [Category.assoc, eV.inv_hom_id, Category.comp_id, ← hh, eU.inv_hom_id_assoc]

variable {F : TopCat.Sheaf AddCommGrpCat.{0} X} (a : F ⟶ K.X 0)
  (ha : a ≫ K.d 0 1 = 0)

theorem abelianCechFlasqueComparison_refinement (n : ℕ) :
    HomologicalComplex.homologyMap (AbelianRefinement.nativeCechRefinement U V r hr F.obj) (n + 1) ≫
      FlasqueCechD.abelianCechFlasqueComparison V hK a ha hV n =
      FlasqueCechD.abelianCechFlasqueComparison U hK a ha hU n := by
  unfold FlasqueCechD.abelianCechFlasqueComparison
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← Intrinsic.CechTotalRefinement.nativeCechVerticalEdge_refinement, HomologicalComplex.homologyMap_comp, Category.assoc,
    nativeFlasqueCechHomologyIso_refinement U V r hr hU hV hK n]

theorem abelianCechToSheaf_refinement (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    HomologicalComplex.homologyMap (AbelianRefinement.nativeCechRefinement U V r hr F.obj) (n + 1) ≫
      Abelian.CechComparison.abelianCechToSheaf V F hV n = Abelian.CechComparison.abelianCechToSheaf U F hU n := by
  rw [← DegreeOneBoundary.abelianCechToSheaf_native V F hV n, ← DegreeOneBoundary.abelianCechToSheaf_native U F hU n,
    ← Category.assoc, abelianCechFlasqueComparison_refinement U V r hr hU hV]

end

/-! Actual literal Cech cocycle classes are unchanged by refinement of their cover. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I J : Type} (U : I → Opens X) (V : J → Opens X)
  (r : J → I) (hr : ∀ j, V j ≤ U (r j))

theorem abelianCechRefinementMap_closed (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (k : Abelian.CechCoordinates.AbelianCechCochain F U n) (hk : Abelian.CechCoordinates.abelianCechDelta F U n k = 0) :
    Abelian.CechCoordinates.abelianCechDelta F V n (AbelianRefinement.abelianCechRefinementMap U V r hr F n k) = 0 := by
  rw [← AbelianRefinement.abelianCechRefinementMap_delta, hk, map_zero]

theorem abelianCechNativeClass_refinement (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (k : Abelian.CechCoordinates.AbelianCechCochain F U (n + 1)) (hk : Abelian.CechCoordinates.abelianCechDelta F U (n + 1) k = 0) :
    HomologicalComplex.homologyMap (AbelianRefinement.nativeCechRefinement U V r hr F) (n + 1)
      (Abelian.CechClasses.abelianCechNativeClass U F n k hk) =
      Abelian.CechClasses.abelianCechNativeClass V F n (AbelianRefinement.abelianCechRefinementMap U V r hr F (n + 1) k)
        (abelianCechRefinementMap_closed U V r hr F (n + 1) k hk) := by
  let f := AbelianRefinement.nativeCechRefinement U V r hr F
  let x := (Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)).symm k
  have hx := Abelian.CechClasses.abelianCechNative_closed U F (n + 1) k hk
  have hy := Intrinsic.DescentCohomology.abelianCochainMap_closed f n x hx
  have he : f.f (n + 1) x = (Abelian.CechCoordinates.abelianCechCoordinates F V (n + 1)).symm
      (AbelianRefinement.abelianCechRefinementMap U V r hr F (n + 1) k) := by
    change (Abelian.CechCoordinates.abelianCechCoordinates F V (n + 1)).symm
      (AbelianRefinement.abelianCechRefinementMap U V r hr F (n + 1)
        (Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1) ((Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)).symm k))) = _
    rw [AddEquiv.apply_symm_apply]
  unfold Abelian.CechClasses.abelianCechNativeClass
  rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk n f x hx hy]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (((CategoryTheory.cechComplexFunctor V).obj F).iCycles (n + 1))).mp
    inferInstance
  rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk]
  exact he

theorem abelianCechSheafClass_refinement (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤) (n : ℕ)
    (k : Abelian.CechCoordinates.AbelianCechCochain F.obj U (n + 1)) (hk : Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) k = 0) :
    Abelian.CechClasses.abelianCechSheafClass V F hV n (AbelianRefinement.abelianCechRefinementMap U V r hr F.obj (n + 1) k)
      (abelianCechRefinementMap_closed U V r hr F.obj (n + 1) k hk) =
      Abelian.CechClasses.abelianCechSheafClass U F hU n k hk := by
  have h := ConcreteCategory.congr_hom (abelianCechToSheaf_refinement U V r hr hU hV F n)
    (Abelian.CechClasses.abelianCechNativeClass U F.obj n k hk)
  change Abelian.CechComparison.abelianCechToSheaf V F hV n
    (HomologicalComplex.homologyMap (AbelianRefinement.nativeCechRefinement U V r hr F.obj) (n + 1)
      (Abelian.CechClasses.abelianCechNativeClass U F.obj n k hk)) = _ at h
  rw [abelianCechNativeClass_refinement] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ClassRefinement
