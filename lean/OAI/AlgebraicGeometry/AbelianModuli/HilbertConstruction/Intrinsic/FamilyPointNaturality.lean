import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyTestPoints
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientProjections

/-! # Family Point Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPointNaturality

noncomputable section

/-! A compatible family of ambient transports induces natural
bijections on actual native-family test points. The comparison is
proved in Cartesian squares, without identifying unequal pullback objects. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} (X : Over S) {T U V : Over S}
variable (a : U ⟶ T) (b : V ⟶ U) (F G : HilbertScheme.Presentations.Hilbert.Functor.Family X T)

private def nativeTestRestriction : Over.mk (b ≫ a).left ⟶ Over.mk a.left :=
  Over.homMk b.left (by rfl)

theorem nativeFamilyPointPullback_ambient
    (x : Over.mk a.left ⟶ FamilyTestPoints.nativeFamilyOver X T F) :
    (FamilyTestPoints.nativeFamilyPointPullback X a F x).left ≫
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F).val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a =
        x.left ≫ F.val.subschemeι := by
  calc
    _ = (FamilyTestPoints.nativeFamilyPointPullback X a F x).left ≫
        (HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val ≫ F.val.subschemeι) :=
      congrArg (fun k => (FamilyTestPoints.nativeFamilyPointPullback X a F x).left ≫ k)
        (HilbertScheme.Presentations.Hilbert.Functor.family_ambient_isPullback X a F.val).w
    _ = ((FamilyTestPoints.nativeFamilyPointPullback X a F x).left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val) ≫
        F.val.subschemeι := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k => k ≫ F.val.subschemeι)
      (FamilyTestPoints.nativeFamilyPointPullback_projection X a F x)

theorem nativeFamilyPointPullback_ambient_natural
    (x : Over.mk a.left ⟶ FamilyTestPoints.nativeFamilyOver X T F) :
    (FamilyTestPoints.nativeFamilyPointPullback X (b ≫ a) F (nativeTestRestriction a b ≫ x)).left ≫
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) F).val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b =
    b.left ≫ (FamilyTestPoints.nativeFamilyPointPullback X a F x).left ≫ (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F).val.subschemeι := by
  let pA : U.left ⟶ (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F).val.subscheme :=
    (FamilyTestPoints.nativeFamilyPointPullback X a F x).left
  let pB : V.left ⟶ (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) F).val.subscheme :=
    (FamilyTestPoints.nativeFamilyPointPullback X (b ≫ a) F (nativeTestRestriction a b ≫ x)).left
  let FA := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F
  let FB := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) F
  have hA : pA ≫ FA.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X U = 𝟙 U.left :=
    (FamilyTestPoints.nativeFamilyPointPullback X a F x).w
  have hB : pB ≫ FB.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X V = 𝟙 V.left :=
    (FamilyTestPoints.nativeFamilyPointPullback X (b ≫ a) F (nativeTestRestriction a b ≫ x)).w
  have hAP : pA ≫ FA.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a = x.left ≫ F.val.subschemeι :=
    nativeFamilyPointPullback_ambient X a F x
  change pB ≫ FB.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b =
    b.left ≫ pA ≫ FA.val.subschemeι
  apply (HilbertScheme.Presentations.Hilbert.Functor.ambient_isPullback X a).hom_ext
  · calc
      _ = (pB ≫ FB.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X V) ≫ b.left := by
        simp only [Category.assoc, HilbertScheme.Presentations.Hilbert.AmbientProjections.ambientMap_projection]
      _ = b.left := by rw [hB, Category.id_comp]
      _ = _ := by simp only [Category.assoc, hA, Category.comp_id]
  · calc
      _ = pB ≫ FB.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X (b ≫ a) := by
        simp only [HilbertScheme.Presentations.Hilbert.Functor.ambientMap_comp, Category.assoc]
      _ = (b.left ≫ x.left) ≫ F.val.subschemeι :=
        nativeFamilyPointPullback_ambient X (b ≫ a) F (nativeTestRestriction a b ≫ x)
      _ = _ := by simp only [Category.assoc, hAP]

theorem nativeFamilyTestPointTransport_natural
    (eA : FamilyTestPoints.nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F) ≅
      FamilyTestPoints.nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a G))
    (eB : FamilyTestPoints.nativeFamilyOver X V (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) F) ≅
      FamilyTestPoints.nativeFamilyOver X V (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) G))
    (EA : HilbertScheme.Presentations.Hilbert.Functor.ambient X U ⟶ HilbertScheme.Presentations.Hilbert.Functor.ambient X U)
    (EB : HilbertScheme.Presentations.Hilbert.Functor.ambient X V ⟶ HilbertScheme.Presentations.Hilbert.Functor.ambient X V)
    (hA : eA.hom.left ≫ (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a G).val.subschemeι =
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F).val.subschemeι ≫ EA)
    (hB : eB.hom.left ≫ (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) G).val.subschemeι =
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) F).val.subschemeι ≫ EB)
    (hE : EB ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b = HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b ≫ EA)
    (x : Over.mk a.left ⟶ FamilyTestPoints.nativeFamilyOver X T F) :
    FamilyTestPoints.nativeFamilyTestPointTransport X (b ≫ a) F G eB (nativeTestRestriction a b ≫ x) =
      nativeTestRestriction a b ≫ FamilyTestPoints.nativeFamilyTestPointTransport X a F G eA x := by
  let pA : U.left ⟶ (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F).val.subscheme :=
    (FamilyTestPoints.nativeFamilyPointPullback X a F x).left
  let pB : V.left ⟶ (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) F).val.subscheme :=
    (FamilyTestPoints.nativeFamilyPointPullback X (b ≫ a) F (nativeTestRestriction a b ≫ x)).left
  let FA := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F
  let FB := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) F
  let GA := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a G
  let GB := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) G
  have hPA : pB ≫ FB.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b =
      b.left ≫ pA ≫ FA.val.subschemeι := nativeFamilyPointPullback_ambient_natural X a b F x
  have hGA : GA.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a =
      HilbertScheme.Presentations.Hilbert.Functor.familyMap X a G.val ≫ G.val.subschemeι := (HilbertScheme.Presentations.Hilbert.Functor.family_ambient_isPullback X a G.val).w
  have hGB : GB.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X (b ≫ a) =
      HilbertScheme.Presentations.Hilbert.Functor.familyMap X (b ≫ a) G.val ≫ G.val.subschemeι :=
    (HilbertScheme.Presentations.Hilbert.Functor.family_ambient_isPullback X (b ≫ a) G.val).w
  apply Over.OverMorphism.ext
  rw [FamilyTestPoints.nativeFamilyTestPointTransport_left]
  change pB ≫ eB.hom.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X (b ≫ a) G.val =
    b.left ≫ (FamilyTestPoints.nativeFamilyTestPointTransport X a F G eA x).left
  rw [FamilyTestPoints.nativeFamilyTestPointTransport_left]
  change pB ≫ eB.hom.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X (b ≫ a) G.val =
    b.left ≫ pA ≫ eA.hom.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a G.val
  apply (cancel_mono G.val.subschemeι).mp
  calc
    _ = pB ≫ (eB.hom.left ≫ GB.val.subschemeι) ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X (b ≫ a) := by
      simp only [Category.assoc, ← hGB]
    _ = pB ≫ FB.val.subschemeι ≫ EB ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X (b ≫ a) := by
      simpa only [Category.assoc] using congrArg (fun c => pB ≫ c ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X (b ≫ a)) hB
    _ = pB ≫ FB.val.subschemeι ≫ (EB ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b) ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a := by
      simp only [HilbertScheme.Presentations.Hilbert.Functor.ambientMap_comp, Category.assoc]
    _ = (pB ≫ FB.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b) ≫ EA ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a := by
      simpa only [Category.assoc] using congrArg (fun c => pB ≫ FB.val.subschemeι ≫ c ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a) hE
    _ = (b.left ≫ pA ≫ FA.val.subschemeι) ≫ EA ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a := congrArg (fun c => c ≫ _) hPA
    _ = b.left ≫ pA ≫ (eA.hom.left ≫ GA.val.subschemeι) ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a := by
      simpa only [Category.assoc] using congrArg (fun c => b.left ≫ pA ≫ c ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a) hA.symm
    _ = (b.left ≫ (pA ≫ eA.hom.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a G.val)) ≫ G.val.subschemeι := by
      simp only [Category.assoc, hGA]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPointNaturality
