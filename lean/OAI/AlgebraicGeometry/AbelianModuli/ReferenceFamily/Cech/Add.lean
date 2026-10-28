import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.DegreeOneBoundary
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.LocalSections
import OAI.AlgebraicGeometry.DivisorClass.Chern.ResolutionQuotient

/-! # Add -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Add

noncomputable section

section

/-! In degree one, a zero sheaf class has an actual Cech primitive on
the original cover. Only left exactness of sheaf sections is needed;
no acyclicity assumption on the members of the cover is introduced. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Sheaf
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology
open _root_.CategoryTheory.Abelian

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

local instance cechBoundaryHasExt : HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  hasExt_of_enoughInjectives _

theorem cechCoefficient_lift_of_exact
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hS : S.Exact) [Mono S.f]
    (n : ℕ) (b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain S.X₂.obj U n)
    (hb : DivisorClass.Chern.Abelian.CechClasses.abelianCechCoefficient U S.g.hom n b = 0) :
    ∃ c : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain S.X₁.obj U n, DivisorClass.Chern.Abelian.CechClasses.abelianCechCoefficient U S.f.hom n c = b := by
  have h (a : Fin (n + 1) → I) :
      ∃ c : S.X₁.obj.obj (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)), S.f.hom.app _ c = b a :=
    TopCat.Sheaf.sections_exact_of_left_exact hS (inferInstance : Mono S.f) _ (congrFun hb a)
  choose c hc using h
  exact ⟨c, funext hc⟩

theorem nativeCech_resolution_zero_lift (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (n : ℕ) (b : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (injectiveResolution F).cocomplex).X 0).X n)
    (hb : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (injectiveResolution F).cocomplex).d 0 1).f n b = 0) :
    ∃ c : ((CategoryTheory.cechComplexFunctor U).obj F.obj).X n,
      ((CategoryTheory.cechComplexFunctor U).map ((injectiveResolution F).ι.f 0).hom).f n c = b := by
  let R := injectiveResolution F
  let β := DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 0).obj U n b
  have hβ : DivisorClass.Chern.Abelian.CechClasses.abelianCechCoefficient U (R.cocomplex.d 0 1).hom n β = 0 := by
    funext a
    have h := congrArg (fun z => DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 1).obj U n z a) hb
    have hn := DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates_naturality (R.cocomplex.X 0).obj U
      (R.cocomplex.d 0 1).hom n b a
    exact hn.symm.trans (h.trans (congrFun (map_zero (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 1).obj U n)) a))
  obtain ⟨c, hc⟩ := cechCoefficient_lift_of_exact U (DivisorClass.Chern.ResolutionQuotient.resolutionZeroSequence R)
    (DivisorClass.Chern.ResolutionQuotient.resolutionZeroSequence_exact R) n β hβ
  refine ⟨(DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F.obj U n).symm c, ?_⟩
  exact (DivisorClass.Chern.Cech.IntrinsicOperators.abelianCechCoordinates_symm_coefficient (F := F.obj) (G := (R.cocomplex.X 0).obj)
    U (show F.obj ⟶ (R.cocomplex.X 0).obj from (R.ι.f 0).hom) n c).trans
      ((congrArg (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 0).obj U n).symm hc).trans
        ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 0).obj U n).symm_apply_apply b))

theorem nativeCech_one_boundary_of_total_boundary (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (k : ((CategoryTheory.cechComplexFunctor U).obj F.obj).X 1)
    (b : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (injectiveResolution F).cocomplex).total (.up ℕ)).X 0)
    (hb : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (injectiveResolution F).cocomplex).total (.up ℕ)).d 0 1 b =
      (DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge U ((injectiveResolution F).ι.f 0)
        (injectiveResolution F).ι_f_zero_comp_complex_d).f 1 k) :
    ∃ c : ((CategoryTheory.cechComplexFunctor U).obj F.obj).X 0,
      ((CategoryTheory.cechComplexFunctor U).obj F.obj).d 0 1 c = k := by
  let R := injectiveResolution F
  let B := SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U R.cocomplex
  let v := DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge U (R.ι.f 0) R.ι_f_zero_comp_complex_d
  let b₀ := (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 0 0 b
  let j := ((CategoryTheory.cechComplexFunctor U).map
    (show F.obj ⟶ (R.cocomplex.X 0).obj from (R.ι.f 0).hom)).f 1
  have hj : v.f 1 = j ≫ B.ιTotal (.up ℕ) 0 1 1 rfl :=
    DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge_f U (R.ι.f 0) R.ι_f_zero_comp_complex_d 1
  have hv₀ : (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 1 0 1 (v.f 1 k) = 0 := by
    have hp : B.ιTotal (.up ℕ) 0 1 1 rfl ≫ (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 1 0 1 = 0 := by
      simp only [(SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat B), show ¬(0 : ℕ) = 1 by decide, dite_false]
    have h : v.f 1 ≫ (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 1 0 1 = 0 := by
      exact (congrArg (fun f => f ≫ (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 1 0 1) hj).trans
        ((Category.assoc j _ _).trans ((congrArg (fun f => j ≫ f) hp).trans (comp_zero)))
    exact ConcreteCategory.congr_hom h k
  have hv₁ : (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 1 1 (v.f 1 k) =
      ((CategoryTheory.cechComplexFunctor U).map (R.ι.f 0).hom).f 1 k := by
    have hp : B.ιTotal (.up ℕ) 0 1 1 rfl ≫ (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 1 1 = 𝟙 _ :=
      (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat_self B) 0 1
    have h : v.f 1 ≫ (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 1 1 =
        ((CategoryTheory.cechComplexFunctor U).map (R.ι.f 0).hom).f 1 := by
      exact (congrArg (fun f => f ≫ (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 1 1) hj).trans
        ((Category.assoc j _ _).trans ((congrArg (fun f => j ≫ f) hp).trans (Category.comp_id j)))
    exact ConcreteCategory.congr_hom h k
  have hd : (B.d 0 1).f 0 b₀ = 0 := by
    have h := ConcreteCategory.congr_hom (SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_zero_right B 0) b
    change (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 1 0 1 ((B.total (.up ℕ)).d 0 1 b) = (B.d 0 1).f 0 b₀ at h
    exact h.symm.trans ((congrArg ((SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 1 0 1) hb).trans hv₀)
  obtain ⟨c, hc⟩ := nativeCech_resolution_zero_lift U F 0 b₀ hd
  refine ⟨c, ?_⟩
  apply (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F.obj U 1).injective
  apply DivisorClass.Chern.Cech.LocalSections.abelianCechCoefficient_injective U (R.ι.f 0) 1
  have hx : (B.X 0).d 0 1 b₀ =
      ((CategoryTheory.cechComplexFunctor U).map (R.ι.f 0).hom).f 1 k := by
    have h := ConcreteCategory.congr_hom (SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_zero B 0) b
    change (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 1 1 ((B.total (.up ℕ)).d 0 1 b) = (B.X 0).d 0 1 b₀ at h
    exact h.symm.trans ((congrArg ((SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 1 1) hb).trans hv₁)
  have hn := ConcreteCategory.congr_hom
    (((CategoryTheory.cechComplexFunctor U).map (R.ι.f 0).hom).comm 0 1) c
  have he : ((CategoryTheory.cechComplexFunctor U).map (R.ι.f 0).hom).f 1
      (((CategoryTheory.cechComplexFunctor U).obj F.obj).d 0 1 c) =
      ((CategoryTheory.cechComplexFunctor U).map (R.ι.f 0).hom).f 1 k := by
    exact hn.symm.trans ((congrArg ((B.X 0).d 0 1) hc).trans hx)
  funext a
  have h := congrArg (fun z => DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 0).obj U 1 z a) he
  have hn₁ := DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates_naturality F.obj U
    (show F.obj ⟶ (R.cocomplex.X 0).obj from (R.ι.f 0).hom) 1
    (((CategoryTheory.cechComplexFunctor U).obj F.obj).d 0 1 c) a
  have hn₂ := DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates_naturality F.obj U
    (show F.obj ⟶ (R.cocomplex.X 0).obj from (R.ι.f 0).hom) 1 k a
  exact hn₁.symm.trans (h.trans hn₂)

theorem cech_one_boundary_of_sheaf_class_zero
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (hU : ⨆ i, U i = ⊤)
    (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U 1) (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U 1 k = 0)
    (hclass : DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU 0 k hk =
      (0 : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1).obj F)) :
    ∃ c : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U 0, DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U 0 c = k := by
  let R := injectiveResolution F
  let K := (CategoryTheory.cechComplexFunctor U).obj F.obj
  let B := SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U R.cocomplex
  let v := DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge U (R.ι.f 0) R.ι_f_zero_comp_complex_d
  let x := (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F.obj U 1).symm k
  have hx : K.d 1 2 x = 0 := DivisorClass.Chern.Abelian.CechClasses.abelianCechNative_closed U F.obj 1 k hk
  have hvx := DivisorClass.Chern.Intrinsic.DescentCohomology.abelianCochainMap_closed v 0 x hx
  have htotal : HomologicalComplex.homologyMap v 1 (DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass U F.obj 0 k hk) = 0 := by
    let e := (DivisorClass.Chern.FlasqueCechD.abelianFlasqueCechHomologyIso U R.cocomplex
      (DivisorClass.Chern.Cech.DegreeOneBoundary.injectiveResolution_flasque F) hU 0).symm ≪≫ DivisorClass.Chern.GammaSectionsComparison.nativeInjectiveCohomologyIso F 0
    apply (AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance
    rw [map_zero]
    have h := ConcreteCategory.congr_hom (DivisorClass.Chern.Cech.DegreeOneBoundary.abelianCechToSheaf_native U F hU 0)
      (DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass U F.obj 0 k hk)
    exact h.trans hclass
  have hz : (B.total (.up ℕ)).homologyπ 1 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 _ (v.f 1 x) hvx) = 0 :=
    (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk 0 v x hx hvx).symm.trans htotal
  obtain ⟨b, hb⟩ := SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.exists_boundary_of_homologyπ_abCyclesMk_eq_zero 0
    (B.total (.up ℕ)) (v.f 1 x) hvx hz
  obtain ⟨c, hc⟩ := nativeCech_one_boundary_of_total_boundary U F x b hb
  refine ⟨DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F.obj U 0 c, ?_⟩
  have h := congrArg (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F.obj U 1) hc
  rw [DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates_d] at h
  exact h.trans ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F.obj U 1).apply_symm_apply k)

end

section

/-! Equal degree-one sheaf classes are related by an actual Cech
change of trivialization on their common cover. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

local instance cechClassAddCommGroup (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H F n) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).obj F))

theorem cechSheafClass_congr (F : TopCat.Sheaf AddCommGrpCat.{0} X) (hU : ⨆ i, U i = ⊤)
    (n : ℕ) (a b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U (n + 1))
    (ha : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) a = 0)
    (hb : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) b = 0) (h : a = b) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU n a ha = DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU n b hb := by
  subst b
  rfl

theorem cech_zero_eq_localSections (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U 0) :
    ∃ s : ∀ i, F.obj.obj (.op (U i)), DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections U F s = b := by
  have hi (i : I) : U i ≤ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (fun _ : Fin 1 => i) := by
    intro x hx
    exact (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection U _ x).mpr (fun _ => hx)
  let s (i : I) := DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict F (hi i) (b (fun _ : Fin 1 => i))
  refine ⟨s, ?_⟩
  funext a
  have ha : (fun _ : Fin 1 => a 0) = a := by
    funext j
    exact congrArg a (Subsingleton.elim 0 j)
  change DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict F _ (DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict F _ (b (fun _ : Fin 1 => a 0))) = b a
  rw [DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp]
  have hres (c : Fin 1 → I) (hc : c = a)
      (hsub : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a ≤ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U c) :
      DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict F hsub (b c) = b a := by
    subst c
    change F.obj.map (𝟙 (.op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))) (b a) = b a
    exact F.obj.map_id_apply (.op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) (b a)
  exact hres _ ha _

theorem cechDelta_sub (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (a b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U n) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n (a - b) = DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n a - DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n b := by
  have h := map_sub (((CategoryTheory.cechComplexFunctor U).obj F).d n (n + 1)).hom
    ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U n).symm a) ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U n).symm b)
  have hh := congrArg (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)) h
  rw [← map_sub, DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates_d, AddEquiv.apply_symm_apply,
    map_sub, DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates_d, DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates_d,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at hh
  exact hh

theorem cechSub_closed (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (a b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U n)
    (ha : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n a = 0) (hb : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n b = 0) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n (a - b) = 0 := by
  rw [cechDelta_sub, ha, hb, sub_self]

theorem cechNativeClass_sub (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (a b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U (n + 1))
    (ha : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U (n + 1) a = 0)
    (hb : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U (n + 1) b = 0) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass U F n (a - b) (cechSub_closed U F (n + 1) a b ha hb) =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass U F n a ha - DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass U F n b hb := by
  let C := (CategoryTheory.cechComplexFunctor U).obj F
  have h : SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n C ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)).symm (a - b))
        (DivisorClass.Chern.Abelian.CechClasses.abelianCechNative_closed U F (n + 1) (a - b) (cechSub_closed U F (n + 1) a b ha hb)) =
      SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n C ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)).symm a)
        (DivisorClass.Chern.Abelian.CechClasses.abelianCechNative_closed U F (n + 1) a ha) -
      SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n C ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)).symm b)
        (DivisorClass.Chern.Abelian.CechClasses.abelianCechNative_closed U F (n + 1) b hb) := by
    apply (AddCommGrpCat.mono_iff_injective (C.iCycles (n + 1))).mp inferInstance
    rw [map_sub (C.iCycles (n + 1)).hom, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk]
    exact map_sub (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)).symm a b
  exact (congrArg (C.homologyπ (n + 1)) h).trans (map_sub (C.homologyπ (n + 1)).hom _ _)

theorem cechSheafClass_sub (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hU : ⨆ i, U i = ⊤) (n : ℕ) (a b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U (n + 1))
    (ha : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) a = 0)
    (hb : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) b = 0) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU n (a - b) (cechSub_closed U F.obj (n + 1) a b ha hb) =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU n a ha - DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU n b hb := by
  exact (congrArg (DivisorClass.Chern.Abelian.CechComparison.abelianCechToSheaf U F hU n) (cechNativeClass_sub U F.obj n a b ha hb)).trans
    (map_sub (DivisorClass.Chern.Abelian.CechComparison.abelianCechToSheaf U F hU n).hom _ _)

theorem cech_one_difference_boundary (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hU : ⨆ i, U i = ⊤) (a b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U 1)
    (ha : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U 1 a = 0) (hb : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U 1 b = 0)
    (h : DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU 0 a ha = DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU 0 b hb) :
    ∃ c : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U 0, DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U 0 c = a - b := by
  apply cech_one_boundary_of_sheaf_class_zero U F hU (a - b) (cechSub_closed U F.obj 1 a b ha hb)
  exact (cechSheafClass_sub U F hU 0 a b ha hb).trans
    ((congrArg (fun z => z - DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU 0 b hb) h).trans (sub_self _))

end

/-! Addition of literal Cech cocycles agrees with addition in their
original native sheaf cohomology. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

local instance cechAdditionCohomologyGroup (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H F n) := cechClassAddCommGroup F n

theorem cechDelta_add (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (a b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U n) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n (a + b) = DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n a + DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n b := by
  have h := map_add (((CategoryTheory.cechComplexFunctor U).obj F).d n (n + 1)).hom
    ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U n).symm a) ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U n).symm b)
  have hh := congrArg (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)) h
  rw [← map_add, DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates_d, AddEquiv.apply_symm_apply,
    map_add, DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates_d, DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates_d,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at hh
  exact hh

theorem cechAdd_closed (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (a b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U n)
    (ha : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n a = 0) (hb : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n b = 0) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n (a + b) = 0 := by
  rw [cechDelta_add, ha, hb, add_zero]

theorem cechNativeClass_add (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (a b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U (n + 1))
    (ha : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U (n + 1) a = 0)
    (hb : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U (n + 1) b = 0) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass U F n (a + b) (cechAdd_closed U F (n + 1) a b ha hb) =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass U F n a ha + DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass U F n b hb := by
  let C := (CategoryTheory.cechComplexFunctor U).obj F
  have h : SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n C ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)).symm (a + b))
        (DivisorClass.Chern.Abelian.CechClasses.abelianCechNative_closed U F (n + 1) (a + b) (cechAdd_closed U F (n + 1) a b ha hb)) =
      SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n C ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)).symm a)
        (DivisorClass.Chern.Abelian.CechClasses.abelianCechNative_closed U F (n + 1) a ha) +
      SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n C ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)).symm b)
        (DivisorClass.Chern.Abelian.CechClasses.abelianCechNative_closed U F (n + 1) b hb) := by
    apply (AddCommGrpCat.mono_iff_injective (C.iCycles (n + 1))).mp inferInstance
    rw [map_add (C.iCycles (n + 1)).hom, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk]
    exact map_add (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)).symm a b
  exact (congrArg (C.homologyπ (n + 1)) h).trans (map_add (C.homologyπ (n + 1)).hom _ _)

theorem cechSheafClass_add (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hU : ⨆ i, U i = ⊤) (n : ℕ) (a b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U (n + 1))
    (ha : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) a = 0)
    (hb : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) b = 0) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU n (a + b) (cechAdd_closed U F.obj (n + 1) a b ha hb) =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU n a ha + DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU n b hb := by
  exact (congrArg (DivisorClass.Chern.Abelian.CechComparison.abelianCechToSheaf U F hU n) (cechNativeClass_add U F.obj n a b ha hb)).trans
    (map_add (DivisorClass.Chern.Abelian.CechComparison.abelianCechToSheaf U F hU n).hom _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Add
