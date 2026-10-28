import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualBasePullbackProjections

/-! # Family Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackComposition

noncomputable section

/-! Canonical native-family pullback isomorphisms commute with composition
and equality of the actual Hilbert families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def nativeFamilyEqIso {S : Scheme.{u}} (X : Over S)
    {T : Over S} {F G : HilbertScheme.Presentations.Hilbert.Functor.Family X T} (h : F = G) :
    FamilyTestPoints.nativeFamilyOver X T F ≅ FamilyTestPoints.nativeFamilyOver X T G :=
  eqToIso (congrArg (FamilyTestPoints.nativeFamilyOver X T) h)

variable {S : Scheme.{u}} (X : Over S) {T U V : Over S}

@[simp]
theorem nativeFamilyEqIso_refl (F : HilbertScheme.Presentations.Hilbert.Functor.Family X T) :
    nativeFamilyEqIso X (rfl : F = F) = Iso.refl _ := rfl

@[reassoc]
theorem nativeFamilyEqIso_hom_ambient {F G : HilbertScheme.Presentations.Hilbert.Functor.Family X T} (h : F = G) :
    (nativeFamilyEqIso X h).hom.left ≫ G.val.subschemeι = F.val.subschemeι := by
  subst G
  exact Category.id_comp _

theorem nativeFamilyEqIso_transport_ambient
    {F F' G G' : HilbertScheme.Presentations.Hilbert.Functor.Family X T} (hF : F = F') (hG : G = G')
    (e : FamilyTestPoints.nativeFamilyOver X T F' ≅ FamilyTestPoints.nativeFamilyOver X T G')
    (A : HilbertScheme.Presentations.Hilbert.Functor.ambient X T ⟶ HilbertScheme.Presentations.Hilbert.Functor.ambient X T)
    (he : e.hom.left ≫ G'.val.subschemeι = F'.val.subschemeι ≫ A) :
    (nativeFamilyEqIso X hF ≪≫ e ≪≫ (nativeFamilyEqIso X hG).symm).hom.left ≫
        G.val.subschemeι = F.val.subschemeι ≫ A := by
  subst F'
  subst G'
  simpa only [nativeFamilyEqIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl] using he

theorem nativeFamilyEqIso_transport_eq
    {F F' G G' : HilbertScheme.Presentations.Hilbert.Functor.Family X T} (hF : F = F') (hG : G = G')
    (e' : FamilyTestPoints.nativeFamilyOver X T F' ≅ FamilyTestPoints.nativeFamilyOver X T G')
    (e : FamilyTestPoints.nativeFamilyOver X T F ≅ FamilyTestPoints.nativeFamilyOver X T G)
    (A : HilbertScheme.Presentations.Hilbert.Functor.ambient X T ⟶ HilbertScheme.Presentations.Hilbert.Functor.ambient X T)
    (he' : e'.hom.left ≫ G'.val.subschemeι = F'.val.subschemeι ≫ A)
    (he : e.hom.left ≫ G.val.subschemeι = F.val.subschemeι ≫ A) :
    nativeFamilyEqIso X hF ≪≫ e' ≪≫ (nativeFamilyEqIso X hG).symm = e := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply (cancel_mono G.val.subschemeι).mp
  exact (nativeFamilyEqIso_transport_ambient X hF hG e' A he').trans he.symm

private theorem composite_diagram {C : Type*} [Category* C]
    {A B D E F G H J : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (q : E ⟶ F)
    (p : F ⟶ G) (r : E ⟶ H) (s : H ⟶ G) (t : D ⟶ J)
    (u : J ⟶ H) (v : J ⟶ G) (w : B ⟶ J)
    (hqp : q ≫ p = r ≫ s) (hhr : h ≫ r = t ≫ u)
    (hus : u ≫ s = v) (hgt : g ≫ t = w) :
    (f ≫ g ≫ h ≫ q) ≫ p = f ≫ w ≫ v := by
  simp only [Category.assoc, hqp]
  rw [← Category.assoc h r s, hhr, Category.assoc t u s, hus,
    ← Category.assoc g t v, hgt]

private theorem nativeFamilyEqIso_familyMap_ambient
    (a : U ⟶ T) (F : HilbertScheme.Presentations.Hilbert.Functor.Family X T) (G : HilbertScheme.Presentations.Hilbert.Functor.Family X U)
    (hG : G = HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F) :
    ((nativeFamilyEqIso X hG).hom.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val) ≫
      F.val.subschemeι = G.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (nativeFamilyEqIso X hG).hom.left ≫ f)
      (HilbertScheme.Presentations.Hilbert.Functor.family_ambient_isPullback X a F.val).w.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a)
          (nativeFamilyEqIso_hom_ambient X hG))))

private theorem equalCompositePullback_hom_fst
    {S T U : Scheme.{u}} (F0 : Over S)
    (a : T ⟶ S) (b : U ⟶ T) (d : U ⟶ S) (hd : b ≫ a = d) :
    (((Over.pullbackComp b a).symm.app F0 ≪≫
      eqToIso (congrArg (fun f => (Over.pullback f).obj F0) hd)).hom.left) ≫
        pullback.fst F0.hom d =
      pullback.fst ((Over.pullback a).obj F0).hom b ≫ pullback.fst F0.hom a := by
  change (((Over.pullbackComp b a).inv.app F0).left ≫
      (eqToIso (congrArg (fun f => (Over.pullback f).obj F0) hd)).hom.left) ≫
        pullback.fst F0.hom d = _
  rw [Category.assoc, EqualBasePullbackProjections.equalBasePullback_hom_fst F0 (b ≫ a) d hd]
  exact (((Over.forget U).mapIso ((Over.pullbackComp b a).app F0)).inv_comp_eq).mpr
    (Pullback.Comparisons.pullbackComp_hom_fst_fst F0 a b).symm

private theorem nativeFamilyEqPullback_hom_fst
    (d : V ⟶ T) (F : HilbertScheme.Presentations.Hilbert.Functor.Family X T) (G : HilbertScheme.Presentations.Hilbert.Functor.Family X V)
    (hG : G = HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X d F) :
    (nativeFamilyEqIso X hG ≪≫ FamilyPullbackIso.nativeFamilyPullbackIso X d F).hom.left ≫
      pullback.fst (FamilyTestPoints.nativeFamilyOver X T F).hom d.left =
      (nativeFamilyEqIso X hG).hom.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X d F.val := by
  simp only [Iso.trans_hom, Over.comp_left]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => (nativeFamilyEqIso X hG).hom.left ≫ f)
      (FamilyPullbackPoints.nativeFamilyPullbackIso_hom_fst X d F))

private theorem nativeFamilyIteratedPullback_hom_fst
    (a : U ⟶ T) (b : V ⟶ U) (d : V ⟶ T)
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family X T) (G : HilbertScheme.Presentations.Hilbert.Functor.Family X V)
    (hG' : G = HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X b (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F))
    (q : (Over.pullback a.left ⋙ Over.pullback b.left).obj (FamilyTestPoints.nativeFamilyOver X T F) ≅
      (Over.pullback d.left).obj (FamilyTestPoints.nativeFamilyOver X T F))
    (hq : q.hom.left ≫ pullback.fst (FamilyTestPoints.nativeFamilyOver X T F).hom d.left =
      pullback.fst ((Over.pullback a.left).obj (FamilyTestPoints.nativeFamilyOver X T F)).hom b.left ≫
        pullback.fst (FamilyTestPoints.nativeFamilyOver X T F).hom a.left) :
    (nativeFamilyEqIso X hG' ≪≫
      FamilyPullbackIso.nativeFamilyPullbackIso X b (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F) ≪≫
      (Over.pullback b.left).mapIso (FamilyPullbackIso.nativeFamilyPullbackIso X a F) ≪≫ q).hom.left ≫
        pullback.fst (FamilyTestPoints.nativeFamilyOver X T F).hom d.left =
      (nativeFamilyEqIso X hG').hom.left ≫
        HilbertScheme.Presentations.Hilbert.Functor.familyMap X b (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F).val ≫
          HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Over.comp_left]
  exact composite_diagram _ _ _ _ _ _ _ _ _ _ _ hq
    (Pullback.Comparisons.overPullback_map_left_fst (FamilyPullbackIso.nativeFamilyPullbackIso X a F).hom b.left)
    (FamilyPullbackPoints.nativeFamilyPullbackIso_hom_fst X a F)
    (FamilyPullbackPoints.nativeFamilyPullbackIso_hom_fst X b (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F))

private theorem threeSquare_cancel {C : Type*} [Category* C]
    {A B D E F G : C} (f : A ⟶ B) (g : A ⟶ D) (b : D ⟶ B)
    (i : B ⟶ E) [Mono i] (j : A ⟶ F) (k : D ⟶ G)
    (d : F ⟶ E) (e : F ⟶ G) (z : G ⟶ E)
    (hl : f ≫ i = j ≫ d) (hr : g ≫ k = j ≫ e)
    (ha : b ≫ i = k ≫ z) (hd : d = e ≫ z) : f = g ≫ b := by
  apply (cancel_mono i).mp
  rw [hl, Category.assoc, ha, ← Category.assoc, hr, Category.assoc, hd]

private theorem nativeFamilyEqIso_familyMap_factor
    (a : U ⟶ T) (b : V ⟶ U) (d : V ⟶ T) (hd : b ≫ a = d)
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family X T) (G : HilbertScheme.Presentations.Hilbert.Functor.Family X V)
    (hG : G = HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X d F)
    (hG' : G = HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X b (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F)) :
    (nativeFamilyEqIso X hG).hom.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X d F.val =
      (nativeFamilyEqIso X hG').hom.left ≫
        HilbertScheme.Presentations.Hilbert.Functor.familyMap X b (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F).val ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val := by
  have hd' : HilbertScheme.Presentations.Hilbert.Functor.ambientMap X d = HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b ≫
      HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a :=
    (congrArg (HilbertScheme.Presentations.Hilbert.Functor.ambientMap X) hd).symm.trans (HilbertScheme.Presentations.Hilbert.Functor.ambientMap_comp X b a)
  have h := threeSquare_cancel _ _ _ F.val.subschemeι _ _ _ _ _
    (nativeFamilyEqIso_familyMap_ambient X d F G hG)
    (nativeFamilyEqIso_familyMap_ambient X b (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F) G hG')
    (HilbertScheme.Presentations.Hilbert.Functor.family_ambient_isPullback X a F.val).w.symm hd'
  exact h.trans (Category.assoc _ _ _)

theorem nativeFamilyPullbackIso_factor
    (a : U ⟶ T) (b : V ⟶ U) (d : V ⟶ T) (hd : b ≫ a = d)
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family X T) (G : HilbertScheme.Presentations.Hilbert.Functor.Family X V)
    (hG : G = HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X d F)
    (hG' : G = HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X b (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F)) :
    nativeFamilyEqIso X hG ≪≫ FamilyPullbackIso.nativeFamilyPullbackIso X d F =
      nativeFamilyEqIso X hG' ≪≫
        FamilyPullbackIso.nativeFamilyPullbackIso X b (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F) ≪≫
        (Over.pullback b.left).mapIso (FamilyPullbackIso.nativeFamilyPullbackIso X a F) ≪≫
        (Over.pullbackComp b.left a.left).symm.app (FamilyTestPoints.nativeFamilyOver X T F) ≪≫
        eqToIso (congrArg
          (fun f : V.left ⟶ T.left => (Over.pullback f).obj (FamilyTestPoints.nativeFamilyOver X T F))
          (congrArg Over.Hom.left hd)) := by
  let F0 := FamilyTestPoints.nativeFamilyOver X T F
  let F1 := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F
  let q := (Over.pullbackComp b.left a.left).symm.app F0 ≪≫
    eqToIso (congrArg
      (fun f : V.left ⟶ T.left => (Over.pullback f).obj F0)
      (congrArg Over.Hom.left hd))
  let eL := nativeFamilyEqIso X hG ≪≫ FamilyPullbackIso.nativeFamilyPullbackIso X d F
  let eR := nativeFamilyEqIso X hG' ≪≫ FamilyPullbackIso.nativeFamilyPullbackIso X b F1 ≪≫
    (Over.pullback b.left).mapIso (FamilyPullbackIso.nativeFamilyPullbackIso X a F) ≪≫ q
  have hq := equalCompositePullback_hom_fst F0 a.left b.left d.left
    (congrArg Over.Hom.left hd)
  have hL := nativeFamilyEqPullback_hom_fst X d F G hG
  have hR := nativeFamilyIteratedPullback_hom_fst X a b d F G hG' q hq
  change eL = eR
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact hL.trans ((nativeFamilyEqIso_familyMap_factor X a b d hd F G hG hG').trans hR.symm)
  · exact eL.hom.w.trans eR.hom.w.symm

theorem nativeFamilyPullbackIso_comp
    (a : U ⟶ T) (b : V ⟶ U) (F : HilbertScheme.Presentations.Hilbert.Functor.Family X T) :
    nativeFamilyEqIso X (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily_comp X b a F).symm ≪≫
        FamilyPullbackIso.nativeFamilyPullbackIso X (b ≫ a) F =
      FamilyPullbackIso.nativeFamilyPullbackIso X b (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F) ≪≫
        (Over.pullback b.left).mapIso (FamilyPullbackIso.nativeFamilyPullbackIso X a F) ≪≫
        (Over.pullbackComp b.left a.left).symm.app (FamilyTestPoints.nativeFamilyOver X T F) := by
  simpa only [nativeFamilyEqIso_refl, eqToIso_refl, Iso.refl_trans,
    Iso.trans_refl] using
    nativeFamilyPullbackIso_factor X a b (b ≫ a) rfl F
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X b (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F))
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily_comp X b a F).symm rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackComposition
