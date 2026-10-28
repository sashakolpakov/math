import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ResolutionInjective
import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.DescentCohomology

/-! # Degree One Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.DegreeOneBoundary

noncomputable section

section

/-! An actual degree-zero total coboundary compares Cech transitions with resolution sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)
  {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}
  {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
  (k : ((CategoryTheory.cechComplexFunctor U).obj F.obj).X 1)
  (s : (FlasqueCechD.abelianDerivedSectionsComplex K).X 1)
  (b : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).X 0).X 0)
  (hb : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).X 0).d 0 1 b =
    ((CategoryTheory.cechComplexFunctor U).map a.hom).f 1 k)
  (hd : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).d 0 1).f 0 b = FlasqueCechD.abelianCechHorizontalAugmentation U K 1 s)

include hb hd in
theorem cechDegreeOne_total_boundary :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).total (.up ℕ)).d 0 1
      ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).ιTotal (.up ℕ) 0 0 0 rfl b) =
      (FlasqueCechD.abelianCechVerticalEdge U a ha).f 1 k -
        (FlasqueCechD.abelianCechHorizontalEdge U K).f 1 (-s) := by
  let B := SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K
  have h := ConcreteCategory.congr_hom ((SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat B) 0 0) b
  simp only [pow_zero, one_smul, AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply] at h
  rw [hb, hd] at h
  rw [FlasqueCechD.abelianCechVerticalEdge_f, FlasqueCechD.abelianCechHorizontalEdge_f]
  change (B.total (.up ℕ)).d 0 1 (B.ιTotal (.up ℕ) 0 0 0 rfl b) =
    B.ιTotal (.up ℕ) 0 1 1 rfl (((CategoryTheory.cechComplexFunctor U).map a.hom).f 1 k) -
      B.ιTotal (.up ℕ) 1 0 1 rfl (FlasqueCechD.abelianCechHorizontalAugmentation U K 1 (-s))
  rw [map_neg, map_neg, sub_neg_eq_add]
  exact h.trans (add_comm _ _)

include hb hd in
theorem cechDegreeOne_total_class
    (hk : ((CategoryTheory.cechComplexFunctor U).obj F.obj).d 1 2 k = 0)
    (hs : (FlasqueCechD.abelianDerivedSectionsComplex K).d 1 2 s = 0) :
    HomologicalComplex.homologyMap (FlasqueCechD.abelianCechVerticalEdge U a ha) 1
      (((CategoryTheory.cechComplexFunctor U).obj F.obj).homologyπ 1
        (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 _ k hk)) =
      HomologicalComplex.homologyMap (FlasqueCechD.abelianCechHorizontalEdge U K) 1
        ((FlasqueCechD.abelianDerivedSectionsComplex K).homologyπ 1
          (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 _ (-s) (by rw [map_neg, hs, neg_zero]))) := by
  let v := FlasqueCechD.abelianCechVerticalEdge U a ha
  let h := FlasqueCechD.abelianCechHorizontalEdge U K
  have hn : (FlasqueCechD.abelianDerivedSectionsComplex K).d 1 2 (-s) = 0 := by rw [map_neg, hs, neg_zero]
  have hv := Intrinsic.DescentCohomology.abelianCochainMap_closed v 0 k hk
  have hh := Intrinsic.DescentCohomology.abelianCochainMap_closed h 0 (-s) hn
  rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk 0 v k hk hv, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk 0 h (-s) hn hh]
  exact SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyπ_cyclesMk_eq_of_sub_eq_boundary 0 _ _ _ hv hh
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).ιTotal (.up ℕ) 0 0 0 rfl b)
    (cechDegreeOne_total_boundary U a ha k s b hb hd).symm

end

section

/-! Degree-one Cech cocycles from local resolution lifts have their computed sheaf class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

theorem injectiveResolution_flasque (F : TopCat.Sheaf AddCommGrpCat.{0} X) (q : ℕ) :
    IsFlasque ((injectiveResolution F).cocomplex.X q) :=
  @SheafCohomology.Cech.Compat.TopCat.Sheaf.IsFlasque.of_injective X _ ((injectiveResolution F).injective q)

theorem abelianCechToSheaf_native (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    FlasqueCechD.abelianCechFlasqueComparison U (injectiveResolution_flasque F)
        ((injectiveResolution F).ι.f 0) (injectiveResolution F).ι_f_zero_comp_complex_d hU n ≫
      (GammaSectionsComparison.nativeInjectiveCohomologyIso F n).hom = Abelian.CechComparison.abelianCechToSheaf U F hU n := by
  unfold FlasqueCechD.abelianCechFlasqueComparison GammaSectionsComparison.nativeInjectiveCohomologyIso
    Abelian.CechComparison.abelianCechToSheaf Abelian.CechComparison.abelianCechToDerived
  simp only [Iso.trans_hom, Category.assoc]
  rfl

variable {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}
  {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
  (k : ((CategoryTheory.cechComplexFunctor U).obj F.obj).X 1)
  (s : (FlasqueCechD.abelianDerivedSectionsComplex K).X 1)
  (b : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).X 0).X 0)
  (hb : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).X 0).d 0 1 b =
    ((CategoryTheory.cechComplexFunctor U).map a.hom).f 1 k)
  (hd : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).d 0 1).f 0 b = FlasqueCechD.abelianCechHorizontalAugmentation U K 1 s)
  (hk : ((CategoryTheory.cechComplexFunctor U).obj F.obj).d 1 2 k = 0)
  (hs : (FlasqueCechD.abelianDerivedSectionsComplex K).d 1 2 s = 0)

include hb hd in
theorem cechDegreeOne_gamma_class (hK : ∀ q, IsFlasque (K.X q)) (hU : ⨆ i, U i = ⊤) :
    FlasqueCechD.abelianCechFlasqueComparison U hK a ha hU 0
      (((CategoryTheory.cechComplexFunctor U).obj F.obj).homologyπ 1 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 _ k hk)) =
      -(FlasqueCechD.abelianDerivedSectionsComplex K).homologyπ 1 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 _ s hs) := by
  have hn : (FlasqueCechD.abelianDerivedSectionsComplex K).d 1 2 (-s) = 0 := by rw [map_neg, hs, neg_zero]
  have he : SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 (FlasqueCechD.abelianDerivedSectionsComplex K) (-s) hn =
      -SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 (FlasqueCechD.abelianDerivedSectionsComplex K) s hs := by
    apply (AddCommGrpCat.mono_iff_injective ((FlasqueCechD.abelianDerivedSectionsComplex K).iCycles 1)).mp inferInstance
    rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, map_neg, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk]
  have h := cechDegreeOne_total_class U a ha k s b hb hd hk hs
  change (FlasqueCechD.abelianFlasqueCechHomologyIso U K hK hU 0).inv
    (HomologicalComplex.homologyMap (FlasqueCechD.abelianCechVerticalEdge U a ha) 1
      (((CategoryTheory.cechComplexFunctor U).obj F.obj).homologyπ 1 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 _ k hk))) = _
  rw [h]
  change (FlasqueCechD.abelianFlasqueCechHomologyIso U K hK hU 0).inv
    ((FlasqueCechD.abelianFlasqueCechHomologyIso U K hK hU 0).hom
      ((FlasqueCechD.abelianDerivedSectionsComplex K).homologyπ 1 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 _ (-s) hn))) = _
  rw [Iso.hom_inv_id_apply, he, map_neg]

end

/-! Two-step Cech descent computes an actual degree-two global resolution class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)
  {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}
  {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
  (k : ((CategoryTheory.cechComplexFunctor U).obj F.obj).X 2)
  (s : (FlasqueCechD.abelianDerivedSectionsComplex K).X 2)
  (b : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).X 0).X 1) (v : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).X 1).X 0)
  (hb : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).X 0).d 1 2 b =
    ((CategoryTheory.cechComplexFunctor U).map a.hom).f 2 k)
  (hd : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).d 0 1).f 1 b = ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).X 1).d 0 1 v)
  (hv : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).d 1 2).f 0 v = FlasqueCechD.abelianCechHorizontalAugmentation U K 2 s)

include hb hd hv in
theorem cechDegreeTwo_total_boundary :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).total (.up ℕ)).d 1 2
      ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).ιTotal (.up ℕ) 0 1 1 rfl b +
        (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).ιTotal (.up ℕ) 1 0 1 rfl v) =
      (FlasqueCechD.abelianCechVerticalEdge U a ha).f 2 k - (FlasqueCechD.abelianCechHorizontalEdge U K).f 2 (-s) := by
  let B := SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K
  have h₀ : (B.total (.up ℕ)).d 1 2 (B.ιTotal (.up ℕ) 0 1 1 rfl b) =
      B.ιTotal (.up ℕ) 1 1 2 rfl ((B.d 0 1).f 1 b) +
        B.ιTotal (.up ℕ) 0 2 2 rfl ((B.X 0).d 1 2 b) := by
    simpa only [pow_zero, one_smul, AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply] using
      (ConcreteCategory.congr_hom ((SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat B) 0 1) b)
  have h₁ : (B.total (.up ℕ)).d 1 2 (B.ιTotal (.up ℕ) 1 0 1 rfl v) =
      B.ιTotal (.up ℕ) 2 0 2 rfl ((B.d 1 2).f 0 v) -
        B.ιTotal (.up ℕ) 1 1 2 rfl ((B.X 1).d 0 1 v) := by
    simpa [ConcreteCategory.comp_apply, Units.smul_def, sub_eq_add_neg] using
      (ConcreteCategory.congr_hom ((SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat B) 1 0) v)
  rw [hd, hb] at h₀
  rw [hv] at h₁
  rw [FlasqueCechD.abelianCechVerticalEdge_f, FlasqueCechD.abelianCechHorizontalEdge_f]
  change (B.total (.up ℕ)).d 1 2
    (B.ιTotal (.up ℕ) 0 1 1 rfl b + B.ιTotal (.up ℕ) 1 0 1 rfl v) =
    B.ιTotal (.up ℕ) 0 2 2 rfl (((CategoryTheory.cechComplexFunctor U).map a.hom).f 2 k) -
      B.ιTotal (.up ℕ) 2 0 2 rfl (FlasqueCechD.abelianCechHorizontalAugmentation U K 2 (-s))
  rw [map_add, h₀, h₁, map_neg, map_neg, sub_neg_eq_add]
  exact (show ∀ c g m : (B.total (.up ℕ)).X 2, (m + c) + (g - m) = c + g from by
    intros; abel) _ _ _

include hb hd hv in
theorem cechDegreeTwo_total_class
    (hk : ((CategoryTheory.cechComplexFunctor U).obj F.obj).d 2 3 k = 0)
    (hs : (FlasqueCechD.abelianDerivedSectionsComplex K).d 2 3 s = 0) :
    HomologicalComplex.homologyMap (FlasqueCechD.abelianCechVerticalEdge U a ha) 2
      (((CategoryTheory.cechComplexFunctor U).obj F.obj).homologyπ 2 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 1 _ k hk)) =
      HomologicalComplex.homologyMap (FlasqueCechD.abelianCechHorizontalEdge U K) 2
        ((FlasqueCechD.abelianDerivedSectionsComplex K).homologyπ 2
          (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 1 _ (-s) (by rw [map_neg, hs, neg_zero]))) := by
  let e := FlasqueCechD.abelianCechVerticalEdge U a ha
  let h := FlasqueCechD.abelianCechHorizontalEdge U K
  have hn : (FlasqueCechD.abelianDerivedSectionsComplex K).d 2 3 (-s) = 0 := by rw [map_neg, hs, neg_zero]
  have he := Intrinsic.DescentCohomology.abelianCochainMap_closed e 1 k hk
  have hh := Intrinsic.DescentCohomology.abelianCochainMap_closed h 1 (-s) hn
  rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk 1 e k hk he, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk 1 h (-s) hn hh]
  exact SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyπ_cyclesMk_eq_of_sub_eq_boundary 1 _ _ _ he hh
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).ιTotal (.up ℕ) 0 1 1 rfl b +
      (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).ιTotal (.up ℕ) 1 0 1 rfl v)
    (cechDegreeTwo_total_boundary U a ha k s b v hb hd hv).symm

include hb hd hv in
theorem cechDegreeTwo_gamma_class
    (hk : ((CategoryTheory.cechComplexFunctor U).obj F.obj).d 2 3 k = 0)
    (hs : (FlasqueCechD.abelianDerivedSectionsComplex K).d 2 3 s = 0)
    (hK : ∀ q, IsFlasque (K.X q)) (hU : ⨆ i, U i = ⊤) :
    FlasqueCechD.abelianCechFlasqueComparison U hK a ha hU 1
      (((CategoryTheory.cechComplexFunctor U).obj F.obj).homologyπ 2 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 1 _ k hk)) =
      -(FlasqueCechD.abelianDerivedSectionsComplex K).homologyπ 2 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 1 _ s hs) := by
  have hn : (FlasqueCechD.abelianDerivedSectionsComplex K).d 2 3 (-s) = 0 := by rw [map_neg, hs, neg_zero]
  have he : SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 1 (FlasqueCechD.abelianDerivedSectionsComplex K) (-s) hn =
      -SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 1 (FlasqueCechD.abelianDerivedSectionsComplex K) s hs := by
    apply (AddCommGrpCat.mono_iff_injective ((FlasqueCechD.abelianDerivedSectionsComplex K).iCycles 2)).mp inferInstance
    rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, map_neg, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk]
  have h := cechDegreeTwo_total_class U a ha k s b v hb hd hv hk hs
  change (FlasqueCechD.abelianFlasqueCechHomologyIso U K hK hU 1).inv
    (HomologicalComplex.homologyMap (FlasqueCechD.abelianCechVerticalEdge U a ha) 2
      (((CategoryTheory.cechComplexFunctor U).obj F.obj).homologyπ 2 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 1 _ k hk))) = _
  rw [h]
  change (FlasqueCechD.abelianFlasqueCechHomologyIso U K hK hU 1).inv
    ((FlasqueCechD.abelianFlasqueCechHomologyIso U K hK hU 1).hom
      ((FlasqueCechD.abelianDerivedSectionsComplex K).homologyπ 2 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 1 _ (-s) hn))) = _
  rw [Iso.hom_inv_id_apply, he, map_neg]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.DegreeOneBoundary
