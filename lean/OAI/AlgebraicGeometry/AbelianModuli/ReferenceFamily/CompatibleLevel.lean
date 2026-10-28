import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Factorization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuasiProjectiveAmpleness
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FiniteEtaleLift
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.QuasiProjectivePresentation

/-! # Compatible Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompatibleLevel.LevelCover

noncomputable section

/-! A compatible full-level parameter scheme over a fixed abelian
scheme. A natural restriction of levels gives a morphism between the
actual full-frame schemes. Its equalizer with a prescribed lower level
is finite etale and classifies compatible levels on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {g L N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {K : Type} [Field K] [CharZero K] (p : S ⟶ Spec (.of K))
  [NeZero L] [NeZero N]

variable (r : Frame.FrameRestriction.LevelCover.fullLevelFamilyFunctor A (N := N) ⟶ Frame.FrameRestriction.LevelCover.fullLevelFamilyFunctor A (N := L))
  (α : A.FullLevel L)

omit p in
theorem fullLevelTransformation_restrict {T U : Over S} (f : T ⟶ U)
    (β : (A.pullback U.hom).FullLevel N) :
    r.app (.op T) (β.restrict (A := A) f) =
      HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.restrict (A := A) (r.app (.op U) β) f := by
  exact NatTrans.naturality_apply (FD := TypeCat.Fun) (CD := fun X : Type 1 => X) r f.op β

def fullFrameMapOfTransformation : Frame.Locus.LevelCover.fullFrameScheme A p (N := N) ⟶ Frame.Locus.LevelCover.fullFrameScheme A p (N := L) :=
  (Frame.Factorization.LevelCover.fullFramePointsEquiv A p (Frame.Locus.LevelCover.fullFrameScheme A p (N := N))).symm
    (r.app (.op (Frame.Locus.LevelCover.fullFrameScheme A p (N := N))) (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel A p))

def fixedFullFrameMap (T : Over S) : T ⟶ Frame.Locus.LevelCover.fullFrameScheme A p (N := L) :=
  (Frame.Factorization.LevelCover.fullFramePointsEquiv A p T).symm (α.pullback T.hom)

theorem fullFrameMapOfTransformation_points {T : Over S}
    (f : T ⟶ Frame.Locus.LevelCover.fullFrameScheme A p (N := N)) :
    Frame.Factorization.LevelCover.fullFramePointsEquiv A p T (f ≫ fullFrameMapOfTransformation A p r) =
      r.app (.op T) (Frame.Factorization.LevelCover.fullFramePointsEquiv A p T f) := by
  have h := (Frame.Factorization.LevelCover.fullFramePointsEquiv A p (Frame.Locus.LevelCover.fullFrameScheme A p (N := N))).apply_symm_apply
    (r.app (.op (Frame.Locus.LevelCover.fullFrameScheme A p (N := N))) (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel A p))
  have hf : Frame.Factorization.LevelCover.fullFramePointsEquiv A p T f = (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel A p).restrict f := rfl
  exact (Frame.Factorization.LevelCover.fullFramePointsEquiv_natural A p f (fullFrameMapOfTransformation A p r)).trans
    ((congrArg (fun β : (A.pullback (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom).FullLevel L =>
      β.restrict f) h).trans
        ((fullLevelTransformation_restrict A r f (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel A p)).symm.trans
          (congrArg (r.app (.op T)) hf.symm)))

theorem fixedFullFrameMap_points {T U : Over S} (f : T ⟶ U) :
    Frame.Factorization.LevelCover.fullFramePointsEquiv A p T (f ≫ fixedFullFrameMap A p α U) = α.pullback T.hom := by
  rw [Frame.Factorization.LevelCover.fullFramePointsEquiv_natural]
  change ((Frame.Factorization.LevelCover.fullFramePointsEquiv A p U)
    ((Frame.Factorization.LevelCover.fullFramePointsEquiv A p U).symm (α.pullback U.hom))).restrict f = _
  rw [Equiv.apply_symm_apply, α.restrict_pullback]

theorem fullFrame_compatible_iff {T : Over S} (f : T ⟶ Frame.Locus.LevelCover.fullFrameScheme A p (N := N)) :
    f ≫ fullFrameMapOfTransformation A p r =
      f ≫ fixedFullFrameMap A p α (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)) ↔
    r.app (.op T) (Frame.Factorization.LevelCover.fullFramePointsEquiv A p T f) = α.pullback T.hom := by
  constructor
  · intro h
    exact (fullFrameMapOfTransformation_points A p r f).symm.trans
      ((congrArg (Frame.Factorization.LevelCover.fullFramePointsEquiv A p T) h).trans (fixedFullFrameMap_points A p α f))
  · intro h
    apply (Frame.Factorization.LevelCover.fullFramePointsEquiv A p T).injective
    exact (fullFrameMapOfTransformation_points A p r f).trans
      (h.trans (fixedFullFrameMap_points A p α f).symm)

def compatibleFullFrameScheme : Over S :=
  equalizer (fullFrameMapOfTransformation A p r)
    (fixedFullFrameMap A p α (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)))

def compatibleFullFrameInclusion : compatibleFullFrameScheme A p r α ⟶ Frame.Locus.LevelCover.fullFrameScheme A p (N := N) :=
  equalizer.ι (fullFrameMapOfTransformation A p r)
    (fixedFullFrameMap A p α (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)))

theorem compatibleFullFrame_finite_etale :
    IsFinite (compatibleFullFrameScheme A p r α).hom ∧
      Etale (compatibleFullFrameScheme A p r α).hom := by
  have : IsFinite (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom := (Frame.Locus.LevelCover.fullFrameScheme_finite_etale A p).1
  have : Etale (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom := (Frame.Locus.LevelCover.fullFrameScheme_finite_etale A p).2
  have : IsFinite (Frame.Locus.LevelCover.fullFrameScheme A p (N := L)).hom := (Frame.Locus.LevelCover.fullFrameScheme_finite_etale A p).1
  have : Etale (Frame.Locus.LevelCover.fullFrameScheme A p (N := L)).hom := (Frame.Locus.LevelCover.fullFrameScheme_finite_etale A p).2
  exact AbelianScheme.TorsionQuotient.FiniteEtaleLift.FiniteEtaleLimits.equalizer_finite_etale _ _

instance compatibleFullFrame_isFinite : IsFinite (compatibleFullFrameScheme A p r α).hom :=
  (compatibleFullFrame_finite_etale A p r α).1

instance compatibleFullFrame_etale : Etale (compatibleFullFrameScheme A p r α).hom :=
  (compatibleFullFrame_finite_etale A p r α).2

theorem compatibleFullFrameInclusion_open_closed :
    IsOpenImmersion (compatibleFullFrameInclusion A p r α).left ∧
      IsClosedImmersion (compatibleFullFrameInclusion A p r α).left := by
  have : IsFinite (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom := (Frame.Locus.LevelCover.fullFrameScheme_finite_etale A p).1
  have : Etale (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom := (Frame.Locus.LevelCover.fullFrameScheme_finite_etale A p).2
  have : IsFinite (Frame.Locus.LevelCover.fullFrameScheme A p (N := L)).hom := (Frame.Locus.LevelCover.fullFrameScheme_finite_etale A p).1
  have : Etale (Frame.Locus.LevelCover.fullFrameScheme A p (N := L)).hom := (Frame.Locus.LevelCover.fullFrameScheme_finite_etale A p).2
  exact AbelianScheme.TorsionQuotient.FiniteEtaleLift.FiniteEtaleLimits.equalizer_open_closed _ _

def compatibleFullFramePointsEquiv (T : Over S) :
    (T ⟶ compatibleFullFrameScheme A p r α) ≃
      {β : (A.pullback T.hom).FullLevel N | r.app (.op T) β = α.pullback T.hom} where
  toFun f := ⟨Frame.Factorization.LevelCover.fullFramePointsEquiv A p T (f ≫ compatibleFullFrameInclusion A p r α),
    (fullFrame_compatible_iff A p r α _).mp (by
      exact (Category.assoc f (compatibleFullFrameInclusion A p r α)
        (fullFrameMapOfTransformation A p r)).trans
          ((congrArg (fun q => f ≫ q) (equalizer.condition (fullFrameMapOfTransformation A p r)
            (fixedFullFrameMap A p α (Frame.Locus.LevelCover.fullFrameScheme A p (N := N))))).trans
              (Category.assoc f (compatibleFullFrameInclusion A p r α)
                (fixedFullFrameMap A p α (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)))).symm))⟩
  invFun β := equalizer.lift ((Frame.Factorization.LevelCover.fullFramePointsEquiv A p T).symm β.val)
    ((fullFrame_compatible_iff A p r α _).mpr (by
      rw [Equiv.apply_symm_apply]
      exact β.property))
  left_inv f := by
    apply equalizer.hom_ext
    rw [equalizer.lift_ι, Equiv.symm_apply_apply]
    rfl
  right_inv β := by
    apply Subtype.ext
    change Frame.Factorization.LevelCover.fullFramePointsEquiv A p T
      (equalizer.lift _ _ ≫ compatibleFullFrameInclusion A p r α) = β.val
    rw [compatibleFullFrameInclusion, equalizer.lift_ι, Equiv.apply_symm_apply]

theorem compatibleFullFramePointsEquiv_natural {T U : Over S} (j : T ⟶ U)
    (f : U ⟶ compatibleFullFrameScheme A p r α) :
    (compatibleFullFramePointsEquiv A p r α T (j ≫ f)).val =
      (compatibleFullFramePointsEquiv A p r α U f).val.restrict j := by
  change Frame.Factorization.LevelCover.fullFramePointsEquiv A p T ((j ≫ f) ≫ compatibleFullFrameInclusion A p r α) = _
  rw [Category.assoc]
  exact Frame.Factorization.LevelCover.fullFramePointsEquiv_natural A p j (f ≫ compatibleFullFrameInclusion A p r α)

def compatibleFullFrameLevel : (A.pullback (compatibleFullFrameScheme A p r α).hom).FullLevel N :=
  Frame.Factorization.LevelCover.fullFramePointsEquiv A p (compatibleFullFrameScheme A p r α) (compatibleFullFrameInclusion A p r α)

theorem compatibleFullFrameLevel_compatible :
    r.app (.op (compatibleFullFrameScheme A p r α)) (compatibleFullFrameLevel A p r α) =
      α.pullback (compatibleFullFrameScheme A p r α).hom :=
  (fullFrame_compatible_iff A p r α (compatibleFullFrameInclusion A p r α)).mp
    (equalizer.condition _ _)

theorem compatibleFullFrameLevel_restrict {T : Over S} (f : T ⟶ compatibleFullFrameScheme A p r α) :
    (compatibleFullFrameLevel A p r α).restrict f = (compatibleFullFramePointsEquiv A p r α T f).val :=
  (Frame.Factorization.LevelCover.fullFramePointsEquiv_natural A p f (compatibleFullFrameInclusion A p r α)).symm

theorem compatibleFullFrame_isAmple (H : HilbertConstruction.Line.Bundles.LineBundle S) (hH : H.IsAmple) :
    (H.pullback (compatibleFullFrameScheme A p r α).hom).IsAmple :=
  hH.pullback_of_isAffineHom (compatibleFullFrameScheme A p r α).hom

theorem compatibleFullFrame_quasiProjective (P : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation (Over.mk p)) :
    Nonempty (HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation ((Over.map p).obj (compatibleFullFrameScheme A p r α))) := by
  have : IsSeparated p := P.separated
  have : S.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have : (compatibleFullFrameScheme A p r α).left.IsSeparated := ⟨by
    rw [← terminal.comp_from (compatibleFullFrameScheme A p r α).hom]
    infer_instance⟩
  have : LocallyOfFiniteType p := P.locallyFiniteType
  exact (compatibleFullFrame_isAmple A p r α (QuasiProjectiveAmpleness.quasiProjectiveAmpleLineBundle P)
    (QuasiProjectiveAmpleness.quasiProjectiveAmpleLineBundle_isAmple P)).exists_quasiProjectivePresentation
      ((compatibleFullFrameScheme A p r α).hom ≫ p)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompatibleLevel.LevelCover
