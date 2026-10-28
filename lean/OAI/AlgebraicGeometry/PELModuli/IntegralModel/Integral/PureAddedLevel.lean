import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.FrameFactorization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.RelativeLevelIso

/-! # Pure Added Level -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PureAddedLevel.IntegralPureModel

noncomputable section

section

/-! Adapted from PureAddedLevelModel at fc4f55b19489ddf8581cc300ef4e451dda22da2e. The base is arbitrary;
invertibility of the prescribed level replaces the characteristic-zero hypothesis. -/

/-! Over a pure HilbertConstruction model, the independently prescribed full level is
constructed by the actual finite-etale full-frame scheme. This supplies
the two-level candidate family without restricting the prescribed N. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.FrameFactorization.IntegralLevelCover

variable {S : Scheme.{0}} {g L N : ℕ} {δ : Fin g → ℕ}
    (M : AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel g δ L S) [NeZero N]
    (hN : ∀ x : M.space.left, IsUnit (N : M.space.left.presheaf.stalk x))

def prescribedFrame : Over M.space.left :=
  FrameLocus.IntegralLevelCover.fullFrameScheme M.universal.abelian hN (N := N)

def addedLevelSpace : Over S :=
  (Over.map M.space.hom).obj (prescribedFrame M hN (N := N))

def addedLevelForget : addedLevelSpace M hN (N := N) ⟶ M.space :=
  Over.homMk (prescribedFrame M hN (N := N)).hom rfl

instance addedLevelForget_isFinite : IsFinite (addedLevelForget M hN (N := N)).left :=
  (FrameLocus.IntegralLevelCover.fullFrameScheme_finite_etale M.universal.abelian hN).1

instance addedLevelForget_etale : Etale (addedLevelForget M hN (N := N)).left :=
  (FrameLocus.IntegralLevelCover.fullFrameScheme_finite_etale M.universal.abelian hN).2

def addedLevelUniversal : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel g δ L N (addedLevelSpace M hN (N := N)).left where
  auxiliary := M.universal.pullback (prescribedFrame M hN (N := N)).hom
  prescribed := CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel M.universal.abelian hN

def liftPrescribedLevel {T : Over S} (f : T ⟶ M.space)
    (β : (M.universal.abelian.pullback f.left).FullLevel N) :
    T ⟶ addedLevelSpace M hN (N := N) := by
  let t : Over M.space.left := Over.mk f.left
  let q := (FrameFactorization.IntegralLevelCover.fullFramePointsEquiv M.universal.abelian hN t).symm β
  exact Over.homMk q.left (by
    exact (Category.assoc q.left (FrameLocus.IntegralLevelCover.fullFrameScheme M.universal.abelian hN).hom
      M.space.hom).symm.trans ((congrArg (fun h => h ≫ M.space.hom) q.w).trans f.w))

theorem liftPrescribedLevel_forget {T : Over S} (f : T ⟶ M.space)
    (β : (M.universal.abelian.pullback f.left).FullLevel N) :
    liftPrescribedLevel M hN f β ≫ addedLevelForget M hN = f := by
  apply Over.OverMorphism.ext
  exact ((FrameFactorization.IntegralLevelCover.fullFramePointsEquiv M.universal.abelian hN (Over.mk f.left)).symm β).w

theorem liftPrescribedLevel_coefficients {T : Over S} (f : T ⟶ M.space)
    (β : (M.universal.abelian.pullback f.left).FullLevel N) :
    (CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel M.universal.abelian hN).restrict
      ((FrameFactorization.IntegralLevelCover.fullFramePointsEquiv M.universal.abelian hN (Over.mk f.left)).symm β) = β :=
  (FrameFactorization.IntegralLevelCover.fullFramePointsEquiv M.universal.abelian hN (Over.mk f.left)).apply_symm_apply β

end

section

/-! Adapted from PureAddedLevelMaps at fc4f55b19489ddf8581cc300ef4e451dda22da2e. The base is arbitrary;
invertibility of the prescribed level replaces the characteristic-zero hypothesis. -/

/-! Classification of two-level pure families by the constructed
finite-etale full-frame scheme over the exact pure HilbertConstruction model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.FrameFactorization.IntegralLevelCover

variable {S : Scheme.{0}}
    {g L N : ℕ} {δ : Fin g → ℕ}
    (M : AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel g δ L S) [NeZero N]
    (hN : ∀ x : M.space.left, IsUnit (N : M.space.left.presheaf.stalk x))

def frameToAddedMap {T : Over S} (f : T ⟶ M.space)
    (q : Over.mk f.left ⟶ prescribedFrame M hN (N := N)) : T ⟶ addedLevelSpace M hN (N := N) :=
  Over.homMk q.left (by
    exact (Category.assoc q.left (prescribedFrame M hN (N := N)).hom M.space.hom).symm.trans
      ((congrArg (fun z => z ≫ M.space.hom) q.w).trans f.w))

def addedMapFrame {T : Over S} (j : T ⟶ addedLevelSpace M hN (N := N))
    (f : T ⟶ M.space) (hf : j ≫ addedLevelForget M hN = f) :
    Over.mk f.left ⟶ prescribedFrame M hN (N := N) :=
  Over.homMk j.left (congrArg (fun z => z.left) hf)

def frameAddedIso {T : Over S} (f : T ⟶ M.space)
    (q : Over.mk f.left ⟶ prescribedFrame M hN (N := N)) :
    AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso ((addedLevelUniversal M hN).pullback (frameToAddedMap M hN f q).left)
      (AbelianModuli.ReferenceFamily.Pure.RelativeLevelIso.relativeAddedLevel M.universal (Over.mk f.left)
        ((CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel M.universal.abelian hN).restrict q)) :=
  AbelianModuli.ReferenceFamily.Pure.RelativeLevelIso.relativeAddedLevelIso M.universal q (CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel M.universal.abelian hN)

end

section

/-! Adapted from PureAddedLevelExistence at fc4f55b19489ddf8581cc300ef4e451dda22da2e. The base is arbitrary;
invertibility of the prescribed level replaces the characteristic-zero hypothesis. -/

/-! Classification of two-level pure families by the constructed
finite-etale full-frame scheme over the exact pure HilbertConstruction model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.FrameFactorization.IntegralLevelCover

variable {S : Scheme.{0}}
    {g L N : ℕ} {δ : Fin g → ℕ}
    (M : AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel g δ L S) [NeZero N]
    (hN : ∀ x : M.space.left, IsUnit (N : M.space.left.presheaf.stalk x))

theorem addedLevel_classifying_exists (hM : M.IsFine)
    (T : Over S) (A : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel g δ L N T.left) :
    ∃ j : T ⟶ addedLevelSpace M hN (N := N),
      Nonempty (AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso ((addedLevelUniversal M hN).pullback j.left) A) := by
  obtain ⟨f, ⟨e⟩, _⟩ := hM T A.auxiliary
  let β : (M.universal.abelian.pullback f.left).FullLevel N :=
    @AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.transport g N T.left A.auxiliary.abelian
      (M.universal.abelian.pullback f.left) A.prescribed e.abelian.symm e.symm.abelianGroup
  let q : Over.mk f.left ⟶ prescribedFrame M hN (N := N) :=
    (FrameFactorization.IntegralLevelCover.fullFramePointsEquiv M.universal.abelian hN (Over.mk f.left)).symm β
  have hβ : (CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel M.universal.abelian hN).restrict q = β :=
    (FrameFactorization.IntegralLevelCover.fullFramePointsEquiv M.universal.abelian hN (Over.mk f.left)).apply_symm_apply β
  refine ⟨frameToAddedMap M hN f q, ⟨(frameAddedIso M hN f q).trans
    { auxiliary := e, prescribed := ?_ }⟩⟩
  apply AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro U c
  have h := congrArg (fun α : (M.universal.abelian.pullback f.left).FullLevel N =>
    (α.hom.app (.op U) c).val ≫ e.abelian.hom) hβ
  exact h.trans (by
    change ((A.prescribed.hom.app (.op U) c).val ≫ e.abelian.inv) ≫ e.abelian.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id])

end

/-! Uniqueness for the constructed integral two-level pure parameter
follows from rigidity of the actual underlying auxiliary-level families.
The rigidity hypothesis is local to this comparison lemma. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.FrameFactorization.IntegralLevelCover

variable {S : Scheme.{0}} {g L N : ℕ} {δ : Fin g → ℕ}
    (M : AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel g δ L S) [NeZero N]
    (hN : ∀ x : M.space.left, IsUnit (N : M.space.left.presheaf.stalk x))

theorem addedLevel_classifying_unique_of_rigidity (hM : M.IsFine)
    (T : Over S) (A : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel g δ L N T.left)
    (hRigid : ∀ (f : T ⟶ M.space)
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback f.left) (M.universal.pullback f.left)),
      e.abelian.hom = 𝟙 (M.universal.abelian.pullback f.left).scheme)
    (j k : T ⟶ addedLevelSpace M hN (N := N))
    (a : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso ((addedLevelUniversal M hN).pullback j.left) A)
    (b : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso ((addedLevelUniversal M hN).pullback k.left) A) : j = k := by
  let f := j ≫ addedLevelForget M hN
  let h := k ≫ addedLevelForget M hN
  let q := addedMapFrame M hN j f rfl
  let r := addedMapFrame M hN k h rfl
  let a' := (frameAddedIso M hN f q).symm.trans a
  let b' := (frameAddedIso M hN h r).symm.trans b
  obtain ⟨u, _, hu⟩ := hM T A.auxiliary
  have hh : h = f := (hu h ⟨b'.auxiliary⟩).trans (hu f ⟨a'.auxiliary⟩).symm
  let r' := addedMapFrame M hN k f hh
  let c := (frameAddedIso M hN f r').symm.trans b
  have hab : a'.auxiliary.abelian.hom = c.auxiliary.abelian.hom := by
    have he := hRigid f (a'.auxiliary.trans c.auxiliary.symm)
    have hh := congrArg (fun z => z ≫ c.auxiliary.abelian.hom) he
    change (a'.auxiliary.abelian.hom ≫ c.auxiliary.abelian.inv) ≫ c.auxiliary.abelian.hom =
      𝟙 (M.universal.abelian.pullback f.left).scheme ≫ c.auxiliary.abelian.hom at hh
    exact ((Category.assoc _ _ _).trans
      ((congrArg (a'.auxiliary.abelian.hom ≫ ·) c.auxiliary.abelian.inv_hom_id).trans
        (Category.comp_id _))).symm.trans (hh.trans (Category.id_comp _))
  let firstLevel := (CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel M.universal.abelian hN).restrict q
  let secondLevel := (CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel M.universal.abelian hN).restrict r'
  have hβ : firstLevel = secondLevel := by
    apply AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
    intro U coefficients
    apply (cancel_mono c.auxiliary.abelian.hom).mp
    exact ((congrArg (fun z => (firstLevel.hom.app (.op U) coefficients).val ≫ z)
      hab).symm.trans (a'.prescribed_basis U coefficients)).trans
        (c.prescribed_basis U coefficients).symm
  have hq : q = r' := (FrameFactorization.IntegralLevelCover.fullFramePointsEquiv M.universal.abelian hN (Over.mk f.left)).injective hβ
  exact Over.OverMorphism.ext (congrArg (fun z => z.left) hq)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PureAddedLevel.IntegralPureModel
