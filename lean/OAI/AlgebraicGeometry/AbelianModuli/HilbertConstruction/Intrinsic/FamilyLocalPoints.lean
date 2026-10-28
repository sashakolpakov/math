import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPointNaturality

/-! # Family Local Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyLocalPoints

noncomputable section

/-! Cartesian comparisons for points of an actual local Hilbert family. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem cartesianLocalSection {C : Type*} [Category* C]
    {A B D T U V : C} {πA : A ⟶ U} {πB : B ⟶ T}
    {a : U ⟶ T} {f : A ⟶ B} (H : IsPullback πA f a πB)
    (πD : D ⟶ V) (b : V ⟶ U) (g : D ⟶ A)
    (sA : V ⟶ A) (sD : V ⟶ D)
    (hA : sA ≫ πA = b) (hD : sD ≫ πD = 𝟙 V)
    (hg : g ≫ πA = πD ≫ b)
    (hs : (sD ≫ g) ≫ f = sA ≫ f) : sD ≫ g = sA := by
  apply H.hom_ext
  · simp only [Category.assoc, hg, ← Category.assoc sD πD b,
      hD, Category.id_comp, hA]
  · exact hs

private theorem localSectionComposite {C : Type*} [Category* C]
    {V A B FA FB F T : C}
    (pA : V ⟶ FA) (pB : V ⟶ FB) (iA : FA ⟶ A) (iB : FB ⟶ B)
    (m : B ⟶ A) (mA : A ⟶ T) (mB : B ⟶ T)
    (p : V ⟶ F) (g : FA ⟶ F) (i : F ⟶ T)
    (hm : mB = m ≫ mA) (hp : p = pA ≫ g)
    (hg : g ≫ i = iA ≫ mA) (hB : pB ≫ iB ≫ mB = p ≫ i) :
    ((pB ≫ iB) ≫ m) ≫ mA = (pA ≫ iA) ≫ mA := by
  simp only [Category.assoc]
  rw [← hm, hB, hp, Category.assoc, hg]

private theorem localAmbientTransport {C : Type*} [Category* C]
    {Z FA FB GA GB G A B T : C}
    (pA : Z ⟶ FA) (pB : Z ⟶ FB) (eA : FA ⟶ GA) (eB : FB ⟶ GB)
    (iFA : FA ⟶ A) (iFB : FB ⟶ B) (iGA : GA ⟶ A) (iGB : GB ⟶ B)
    (gA : GA ⟶ G) (gB : GB ⟶ G) (iG : G ⟶ T) [Mono iG]
    (m : B ⟶ A) (mA : A ⟶ T) (mB : B ⟶ T) (EA : A ⟶ A) (EB : B ⟶ B)
    (hA : eA ≫ iGA = iFA ≫ EA) (hB : eB ≫ iGB = iFB ≫ EB)
    (hE : EB ≫ m = m ≫ EA) (hP : pB ≫ iFB ≫ m = pA ≫ iFA)
    (hgA : gA ≫ iG = iGA ≫ mA) (hgB : gB ≫ iG = iGB ≫ mB)
    (hm : mB = m ≫ mA) : pB ≫ eB ≫ gB = pA ≫ eA ≫ gA := by
  apply (cancel_mono iG).mp
  simp only [Category.assoc, hgA, hgB]
  rw [← Category.assoc eA iGA mA, ← Category.assoc eB iGB mB, hA, hB]
  simp only [Category.assoc, hm]
  rw [← Category.assoc EB m mA, hE]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ EA ≫ mA) hP

variable {S : Scheme.{u}} (X : Over S) {T U V : Over S}
variable (a : U ⟶ T) (b : V ⟶ U)

theorem nativeFamilyPointPullback_from_local_ambient
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family X T)
    (x : V.left ⟶
      (FamilyTestPoints.nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F)).left)
    (hx : x ≫
      (FamilyTestPoints.nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F)).hom = b.left)
    (p : Over.mk ((b ≫ a).left) ⟶ FamilyTestPoints.nativeFamilyOver X T F)
    (hp : p.left = x ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val) :
    (FamilyTestPoints.nativeFamilyPointPullback X (b ≫ a) F p).left ≫
        (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) F).val.subschemeι ≫
          HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b =
      x ≫ (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F).val.subschemeι := by
  let FA := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F
  let FB := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) F
  let z := FamilyTestPoints.nativeFamilyPointPullback X (b ≫ a) F p
  have hz :
      z.left ≫ FB.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X V =
        𝟙 V.left := z.w
  have hx' :
      x ≫ FA.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X U =
        b.left := hx
  have hs := localSectionComposite x z.left FA.val.subschemeι FB.val.subschemeι
    (HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b) (HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a) (HilbertScheme.Presentations.Hilbert.Functor.ambientMap X (b ≫ a))
    p.left (HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val) F.val.subschemeι
    (HilbertScheme.Presentations.Hilbert.Functor.ambientMap_comp X b a) hp
    (HilbertScheme.Presentations.Hilbert.Functor.family_ambient_isPullback X a F.val).w.symm
    (FamilyPointNaturality.nativeFamilyPointPullback_ambient X (b ≫ a) F p)
  exact cartesianLocalSection (HilbertScheme.Presentations.Hilbert.Functor.ambient_isPullback X a)
    (HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X V) b.left (HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b)
    (x ≫ FA.val.subschemeι) (z.left ≫ FB.val.subschemeι)
    ((Category.assoc _ _ _).trans hx') ((Category.assoc _ _ _).trans hz)
    (HilbertScheme.Presentations.Hilbert.AmbientProjections.ambientMap_projection X b) hs

theorem nativeFamilyTestPointTransport_from_local
    (F G : HilbertScheme.Presentations.Hilbert.Functor.Family X T)
    (eA : FamilyTestPoints.nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F) ≅
      FamilyTestPoints.nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a G))
    (eB : FamilyTestPoints.nativeFamilyOver X V (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) F) ≅
      FamilyTestPoints.nativeFamilyOver X V (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) G))
    (EA : HilbertScheme.Presentations.Hilbert.Functor.ambient X U ⟶ HilbertScheme.Presentations.Hilbert.Functor.ambient X U)
    (EB : HilbertScheme.Presentations.Hilbert.Functor.ambient X V ⟶ HilbertScheme.Presentations.Hilbert.Functor.ambient X V)
    (hA : eA.hom.left ≫
        (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a G).val.subschemeι =
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F).val.subschemeι ≫ EA)
    (hB : eB.hom.left ≫
        (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) G).val.subschemeι =
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) F).val.subschemeι ≫ EB)
    (hE : EB ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b =
      HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b ≫ EA)
    (x : V.left ⟶
      (FamilyTestPoints.nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F)).left)
    (hx : x ≫
      (FamilyTestPoints.nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F)).hom = b.left)
    (p : Over.mk ((b ≫ a).left) ⟶ FamilyTestPoints.nativeFamilyOver X T F)
    (hp : p.left = x ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val) :
    (FamilyTestPoints.nativeFamilyTestPointTransport X (b ≫ a) F G eB p).left =
      x ≫ eA.hom.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a G.val := by
  let z := FamilyTestPoints.nativeFamilyPointPullback X (b ≫ a) F p
  have h := localAmbientTransport x z.left eA.hom.left eB.hom.left
    (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F).val.subschemeι
    (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) F).val.subschemeι
    (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a G).val.subschemeι
    (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X (b ≫ a) G).val.subschemeι
    (HilbertScheme.Presentations.Hilbert.Functor.familyMap X a G.val) (HilbertScheme.Presentations.Hilbert.Functor.familyMap X (b ≫ a) G.val) G.val.subschemeι
    (HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b) (HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a) (HilbertScheme.Presentations.Hilbert.Functor.ambientMap X (b ≫ a)) EA EB
    hA hB hE (nativeFamilyPointPullback_from_local_ambient X a b F x hx p hp)
    (HilbertScheme.Presentations.Hilbert.Functor.family_ambient_isPullback X a G.val).w.symm
    (HilbertScheme.Presentations.Hilbert.Functor.family_ambient_isPullback X (b ≫ a) G.val).w.symm
    (HilbertScheme.Presentations.Hilbert.Functor.ambientMap_comp X b a)
  exact (FamilyTestPoints.nativeFamilyTestPointTransport_left X (b ≫ a) F G eB p).trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyLocalPoints
