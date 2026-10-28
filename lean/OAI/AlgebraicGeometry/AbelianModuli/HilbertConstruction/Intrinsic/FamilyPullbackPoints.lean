import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackIso

/-! # Family Pullback Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackPoints

noncomputable section

/-! Canonical family pullback isomorphisms retain the actual maps on
every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (X : Over S) {T U : Over S}
variable (a : U ⟶ T) (F : HilbertScheme.Presentations.Hilbert.Functor.Family X T)

@[reassoc]
theorem nativeFamilyPullbackIso_hom_fst :
    (FamilyPullbackIso.nativeFamilyPullbackIso X a F).hom.left ≫
        pullback.fst (FamilyTestPoints.nativeFamilyOver X T F).hom a.left = HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val :=
  (HilbertScheme.Presentations.Hilbert.Functor.family_isPullback X a F.val).flip.isoPullback_hom_fst

@[reassoc]
theorem nativeFamilyPullbackIso_inv_familyMap :
    (FamilyPullbackIso.nativeFamilyPullbackIso X a F).inv.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val =
      pullback.fst (FamilyTestPoints.nativeFamilyOver X T F).hom a.left :=
  (HilbertScheme.Presentations.Hilbert.Functor.family_isPullback X a F.val).flip.isoPullback_inv_fst

theorem nativeFamilyPullbackIso_point (x : Over.mk a.left ⟶ FamilyTestPoints.nativeFamilyOver X T F) :
    (FamilyTestPoints.nativeFamilyPointPullback X a F x).left ≫ (FamilyPullbackIso.nativeFamilyPullbackIso X a F).hom.left =
      pullback.lift x.left (𝟙 U.left) (x.w.trans (Category.id_comp a.left).symm) := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => (FamilyTestPoints.nativeFamilyPointPullback X a F x).left ≫ f)
        (nativeFamilyPullbackIso_hom_fst X a F)).trans
        ((FamilyTestPoints.nativeFamilyPointPullback_projection X a F x).trans
          (pullback.lift_fst _ _ _).symm))
  · have hw : (FamilyPullbackIso.nativeFamilyPullbackIso X a F).hom.left ≫
        pullback.snd (FamilyTestPoints.nativeFamilyOver X T F).hom a.left =
        (FamilyTestPoints.nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F)).hom :=
      (FamilyPullbackIso.nativeFamilyPullbackIso X a F).hom.w
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => (FamilyTestPoints.nativeFamilyPointPullback X a F x).left ≫ f) hw).trans
        ((FamilyTestPoints.nativeFamilyPointPullback X a F x).w.trans
          (pullback.lift_snd _ _ _).symm))

variable (G : HilbertScheme.Presentations.Hilbert.Functor.Family X T)

def nativeFamilyIsoPullback (e : FamilyTestPoints.nativeFamilyOver X T F ≅ FamilyTestPoints.nativeFamilyOver X T G) :
    FamilyTestPoints.nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F) ≅
      FamilyTestPoints.nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a G) :=
  FamilyPullbackIso.nativeFamilyPullbackIso X a F ≪≫ (Over.pullback a.left).mapIso e ≪≫
    (FamilyPullbackIso.nativeFamilyPullbackIso X a G).symm

@[reassoc]
theorem nativeFamilyIsoPullback_familyMap
    (e : FamilyTestPoints.nativeFamilyOver X T F ≅ FamilyTestPoints.nativeFamilyOver X T G) :
    (nativeFamilyIsoPullback X a F G e).hom.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a G.val =
      HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val ≫ e.hom.left := by
  have hm : ((Over.pullback a.left).map e.hom).left ≫
        pullback.fst (FamilyTestPoints.nativeFamilyOver X T G).hom a.left =
      pullback.fst (FamilyTestPoints.nativeFamilyOver X T F).hom a.left ≫ e.hom.left :=
    pullback.lift_fst _ _ _
  change ((FamilyPullbackIso.nativeFamilyPullbackIso X a F).hom.left ≫
      ((Over.pullback a.left).map e.hom).left ≫ (FamilyPullbackIso.nativeFamilyPullbackIso X a G).inv.left) ≫
      HilbertScheme.Presentations.Hilbert.Functor.familyMap X a G.val = HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val ≫ e.hom.left
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (FamilyPullbackIso.nativeFamilyPullbackIso X a F).hom.left ≫ f)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => ((Over.pullback a.left).map e.hom).left ≫ f)
          (nativeFamilyPullbackIso_inv_familyMap X a G)).trans hm))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ e.hom.left)
          (nativeFamilyPullbackIso_hom_fst X a F))))

theorem nativeFamilyIsoPullback_points
    (e : FamilyTestPoints.nativeFamilyOver X T F ≅ FamilyTestPoints.nativeFamilyOver X T G)
    (x : Over.mk a.left ⟶ FamilyTestPoints.nativeFamilyOver X T F) :
    FamilyTestPoints.nativeFamilyTestPointTransport X a F G (nativeFamilyIsoPullback X a F G e) x =
      x ≫ e.hom := by
  apply Over.OverMorphism.ext
  change (FamilyTestPoints.nativeFamilyTestPointTransport X a F G (nativeFamilyIsoPullback X a F G e) x).left =
    x.left ≫ e.hom.left
  exact (FamilyTestPoints.nativeFamilyTestPointTransport_left X a F G _ x).trans
    ((congrArg (fun f => (FamilyTestPoints.nativeFamilyPointPullback X a F x).left ≫ f)
      (nativeFamilyIsoPullback_familyMap X a F G e)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ e.hom.left)
          (FamilyTestPoints.nativeFamilyPointPullback_projection X a F x))))

theorem nativeFamilyIsoPullback_eq_of_familyMap
    (e : FamilyTestPoints.nativeFamilyOver X T F ≅ FamilyTestPoints.nativeFamilyOver X T G)
    (e' : FamilyTestPoints.nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F) ≅
      FamilyTestPoints.nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a G))
    (h : HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val ≫ e.hom.left =
      e'.hom.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a G.val) : nativeFamilyIsoPullback X a F G e = e' := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply (HilbertScheme.Presentations.Hilbert.Functor.family_isPullback X a G.val).hom_ext
  · exact (nativeFamilyIsoPullback X a F G e).hom.w.trans e'.hom.w.symm
  · exact (nativeFamilyIsoPullback_familyMap X a F G e).trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackPoints
