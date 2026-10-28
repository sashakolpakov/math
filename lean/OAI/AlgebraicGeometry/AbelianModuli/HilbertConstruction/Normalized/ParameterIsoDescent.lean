import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BundleIsoOpenDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.ZeroNormalizedBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphPowerOpenCover

/-! # Parameter Iso Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.ParameterIsoDescent.AbelianScheme

noncomputable section

/-! Normalized line-bundle compatibility descends through an open cover.
Local raw line isomorphisms suffice because the zero fibers have their
canonical trivializations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u

private theorem pullback_class_square
    {X Y U V : Scheme.{u}} (a : U ⟶ X) (b : V ⟶ Y) (e : X ⟶ Y) (f : U ⟶ V)
    (h : a ≫ e = f ≫ b)
    (L : Line.Bundles.LineBundle.IsoClass X) (M : Line.Bundles.LineBundle.IsoClass Y)
    (L' : Line.Bundles.LineBundle.IsoClass U) (M' : Line.Bundles.LineBundle.IsoClass V)
    (ha : Line.Bundles.LineBundle.pullbackClass a L = L') (hb : Line.Bundles.LineBundle.pullbackClass b M = M')
    (hf : Line.Bundles.LineBundle.pullbackClass f M' = L') :
    Line.Bundles.LineBundle.pullbackClass a (Line.Bundles.LineBundle.pullbackClass e M) = Line.Bundles.LineBundle.pullbackClass a L := by
  calc
    _ = Line.Bundles.LineBundle.pullbackClass (a ≫ e) M := (Line.Bundles.LineBundle.pullbackClass_comp a e M).symm
    _ = Line.Bundles.LineBundle.pullbackClass (f ≫ b) M := congrArg (fun z => Line.Bundles.LineBundle.pullbackClass z M) h
    _ = Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.pullbackClass b M) := Line.Bundles.LineBundle.pullbackClass_comp f b M
    _ = Line.Bundles.LineBundle.pullbackClass f M' := congrArg (Line.Bundles.LineBundle.pullbackClass f) hb
    _ = L' := hf
    _ = _ := ha.symm

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

private theorem normalized_baseChange_class {T : Scheme.{u}}
    (L : Line.Bundles.LineBundle A.scheme.left) (f : T ⟶ S) :
    Line.Bundles.LineBundle.classOf ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom f)) =
      Line.Bundles.LineBundle.classOf ((A.pullback f).zeroNormalizedBundle
        (L.pullback (pullback.fst A.scheme.hom f))) :=
  Quotient.sound ⟨A.zeroNormalizedBundle_baseChangeIso L f⟩

private theorem normalized_group_class {B : Abelian.Schemes.AbelianScheme g S}
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (M : Line.Bundles.LineBundle B.scheme.left) :
    Line.Bundles.LineBundle.classOf ((B.zeroNormalizedBundle M).pullback e.hom.left) =
      Line.Bundles.LineBundle.classOf (A.zeroNormalizedBundle (M.pullback e.hom.left)) :=
  Quotient.sound ⟨A.zeroNormalizedBundle_groupIso e M⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.zeroNormalizedBundle_class_transport {B : Abelian.Schemes.AbelianScheme g S}
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (L : Line.Bundles.LineBundle A.scheme.left) (M : Line.Bundles.LineBundle B.scheme.left)
    (h : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf M) = Line.Bundles.LineBundle.classOf L) :
    Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf (B.zeroNormalizedBundle M)) =
      Line.Bundles.LineBundle.classOf (A.zeroNormalizedBundle L) :=
  (normalized_group_class A e M).trans
    ((Line.Bundles.LineBundle.classOf_sectionNormalized A.scheme.hom η[A.scheme].left (M.pullback e.hom.left)).trans
      ((congrArg (Line.Bundles.LineBundle.sectionNormalizeClass A.scheme.hom η[A.scheme].left) h).trans
        (Line.Bundles.LineBundle.classOf_sectionNormalized A.scheme.hom η[A.scheme].left L).symm))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.zeroNormalizedBundle_iso_of_openCover [IsLocallyNoetherian S]
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L M : Line.Bundles.LineBundle A.scheme.left)
    (C : S.OpenCover.{u})
    (h : ∀ i, Nonempty ((L.pullback (pullback.fst A.scheme.hom (C.f i))).sheaf ≅
      (M.pullback (pullback.fst A.scheme.hom (C.f i))).sheaf)) :
    Nonempty ((A.zeroNormalizedBundle L).sheaf ≅ (A.zeroNormalizedBundle M).sheaf) := by
  apply Projective.BundleIsoOpenDescent.projective_bundleIso_of_openCover P η[A.scheme].left η[A.scheme].w
    (A.zeroNormalizedBundle L) (A.zeroNormalizedBundle M)
    (A.zeroNormalizedBundle_zeroIso L ≪≫ (A.zeroNormalizedBundle_zeroIso M).symm) C
  intro i
  let B := A.pullback (C.f i)
  let a := pullback.fst A.scheme.hom (C.f i)
  have hraw : Line.Bundles.LineBundle.classOf (L.pullback a) = Line.Bundles.LineBundle.classOf (M.pullback a) := Quotient.sound (h i)
  have hn : Line.Bundles.LineBundle.classOf (B.zeroNormalizedBundle (L.pullback a)) =
      Line.Bundles.LineBundle.classOf (B.zeroNormalizedBundle (M.pullback a)) :=
    (Line.Bundles.LineBundle.classOf_sectionNormalized B.scheme.hom η[B.scheme].left (L.pullback a)).trans
      ((congrArg (Line.Bundles.LineBundle.sectionNormalizeClass B.scheme.hom η[B.scheme].left) hraw).trans
        (Line.Bundles.LineBundle.classOf_sectionNormalized B.scheme.hom η[B.scheme].left (M.pullback a)).symm)
  exact Quotient.exact (s := Line.Bundles.LineBundle.isoSetoid _)
    (a := (A.zeroNormalizedBundle L).pullback a) (b := (A.zeroNormalizedBundle M).pullback a)
    ((normalized_baseChange_class A L (C.f i)).trans
      (hn.trans (normalized_baseChange_class A M (C.f i)).symm))

/-- Base-change normalization and group transport commute on actual
bundle classes. The two model bases may be different. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.zeroNormalizedParameter_class_transport
    {Z T : Scheme.{u}} (B : Abelian.Schemes.AbelianScheme g Z)
    (L : Line.Bundles.LineBundle A.scheme.left) (M : Line.Bundles.LineBundle B.scheme.left)
    (a : T ⟶ S) (b : T ⟶ Z)
    (e : (A.pullback a).scheme ≅ (B.pullback b).scheme) [IsMonHom e.hom]
    (h : Line.Bundles.LineBundle.pullbackClass e.hom.left
        (Line.Bundles.LineBundle.classOf (M.pullback (pullback.fst B.scheme.hom b))) =
      Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst A.scheme.hom a))) :
    Line.Bundles.LineBundle.pullbackClass e.hom.left
        (Line.Bundles.LineBundle.classOf ((B.zeroNormalizedBundle M).pullback (pullback.fst B.scheme.hom b))) =
      Line.Bundles.LineBundle.classOf ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom a)) :=
  (congrArg (Line.Bundles.LineBundle.pullbackClass e.hom.left)
    (normalized_baseChange_class B M b)).trans
    (((A.pullback a).zeroNormalizedBundle_class_transport e _ _ h).trans
      (normalized_baseChange_class A L a).symm)

/-- Local raw compatibility of a natural family comparison implies
its global normalized compatibility. This does not assert descent of
unnormalized line-bundle isomorphisms. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.zeroNormalizedParameter_class_of_openCover
    {T : Scheme.{u}} [IsLocallyNoetherian T]
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (a b : T ⟶ S) (e : (A.pullback a).scheme ≅ (A.pullback b).scheme) [IsMonHom e.hom]
    (C : T.OpenCover.{u}) (a' b' : ∀ i, C.X i ⟶ S)
    (ha : ∀ i, C.f i ≫ a = a' i) (hb : ∀ i, C.f i ≫ b = b' i)
    (e' : ∀ i, (A.pullback (a' i)).scheme ≅ (A.pullback (b' i)).scheme)
    (hn : ∀ i, Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk (C.f i) (ha i) : Over.mk (a' i) ⟶ Over.mk a) A.scheme ≫ e.hom.left =
      (e' i).hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk (C.f i) (hb i) : Over.mk (b' i) ⟶ Over.mk b) A.scheme)
    (hl : ∀ i, Line.Bundles.LineBundle.pullbackClass (e' i).hom.left
        (Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst A.scheme.hom (b' i)))) =
      Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst A.scheme.hom (a' i)))) :
    Line.Bundles.LineBundle.pullbackClass e.hom.left
        (Line.Bundles.LineBundle.classOf ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom b))) =
      Line.Bundles.LineBundle.classOf ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom a)) := by
  let B := A.pullback a
  let La := L.pullback (pullback.fst A.scheme.hom a)
  let Lb := L.pullback (pullback.fst A.scheme.hom b)
  let M := Lb.pullback e.hom.left
  have hm : Nonempty ((B.zeroNormalizedBundle M).sheaf ≅ (B.zeroNormalizedBundle La).sheaf) := by
    apply B.zeroNormalizedBundle_iso_of_openCover (P.baseChange a) M La C
    intro i
    let ca : Over.mk (a' i) ⟶ Over.mk a := Over.homMk (C.f i) (ha i)
    let cb : Over.mk (b' i) ⟶ Over.mk b := Over.homMk (C.f i) (hb i)
    apply GraphPowerOpenCover.bundleIso_of_singleParameterPullback A.scheme ca M La
    have hpa : Line.Bundles.LineBundle.pullbackClass (Single.ParameterBaseChange.singleParameterBaseChangeMap ca A.scheme)
        (Line.Bundles.LineBundle.classOf La) = Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst A.scheme.hom (a' i))) :=
      (Line.Bundles.LineBundle.pullbackClass_comp _ _ (Line.Bundles.LineBundle.classOf L)).symm.trans
        (congrArg (fun f => Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.classOf L))
          (Single.ParameterBaseChange.singleParameterBaseChangeMap_comp ca A.scheme))
    have hpb : Line.Bundles.LineBundle.pullbackClass (Single.ParameterBaseChange.singleParameterBaseChangeMap cb A.scheme)
        (Line.Bundles.LineBundle.classOf Lb) = Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst A.scheme.hom (b' i))) :=
      (Line.Bundles.LineBundle.pullbackClass_comp _ _ (Line.Bundles.LineBundle.classOf L)).symm.trans
        (congrArg (fun f => Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.classOf L))
          (Single.ParameterBaseChange.singleParameterBaseChangeMap_comp cb A.scheme))
    apply Quotient.exact (s := Line.Bundles.LineBundle.isoSetoid _)
      (a := M.pullback (Single.ParameterBaseChange.singleParameterBaseChangeMap ca A.scheme))
      (b := La.pullback (Single.ParameterBaseChange.singleParameterBaseChangeMap ca A.scheme))
    change Line.Bundles.LineBundle.pullbackClass (Single.ParameterBaseChange.singleParameterBaseChangeMap ca A.scheme)
        (Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf Lb)) =
      Line.Bundles.LineBundle.pullbackClass (Single.ParameterBaseChange.singleParameterBaseChangeMap ca A.scheme) (Line.Bundles.LineBundle.classOf La)
    exact pullback_class_square (Single.ParameterBaseChange.singleParameterBaseChangeMap ca A.scheme)
      (Single.ParameterBaseChange.singleParameterBaseChangeMap cb A.scheme) e.hom.left (e' i).hom.left (hn i)
      (Line.Bundles.LineBundle.classOf La) (Line.Bundles.LineBundle.classOf Lb)
      (Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst A.scheme.hom (a' i))))
      (Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst A.scheme.hom (b' i)))) hpa hpb (hl i)
  exact (congrArg (Line.Bundles.LineBundle.pullbackClass e.hom.left)
    (normalized_baseChange_class A L b)).trans
    ((normalized_group_class B e Lb).trans
      ((Quotient.sound (s := Line.Bundles.LineBundle.isoSetoid _)
        (a := B.zeroNormalizedBundle M) (b := B.zeroNormalizedBundle La) hm).trans
          (normalized_baseChange_class A L a).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.ParameterIsoDescent.AbelianScheme
