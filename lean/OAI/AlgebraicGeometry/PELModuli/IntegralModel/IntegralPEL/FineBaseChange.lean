import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.ScalarRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.RelativePullback

/-! # Fine Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FineBaseChange

noncomputable section

/-! Fine integral PEL classification on reduced tests survives arbitrary
coefficient change with the actual base-changed universal family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}

theorem integralPEL_action_baseChange_classifying_iff (φ : R →+* R')
    (U : PEL.Has.IntegralPELObject P R iotaO N X) (Y : Over (Spec (.of R')))
    (A : PEL.Has.IntegralPELObject P R' (φ.comp iotaO) N Y)
    (f : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X) :
    Nonempty (PEL.Iso.PolarizedActionIso ((U.baseChange φ).pullback f).data A.data) ↔
      Nonempty (PEL.Iso.PolarizedActionIso
        (U.pullback (((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom φ))).homEquiv Y X).symm f)).data
        (A.restrictScalars φ Y).data) := by
  let q := pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))
  constructor
  · rintro ⟨e⟩
    exact ⟨(PEL.Iso.PolarizedActionIso.pullbackComp U.data q f.left).symm.trans e⟩
  · rintro ⟨e⟩
    exact ⟨(PEL.Iso.PolarizedActionIso.pullbackComp U.data q f.left).trans e⟩

theorem integralPEL_fine_baseChange
    (U : PEL.Has.IntegralPELObject P R iotaO N X)
    (hU : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (A : PEL.Has.IntegralPELObject P R iotaO N T),
      ∃! f : T ⟶ X, Nonempty (PEL.Iso.PolarizedActionIso (U.pullback f).data A.data))
    (φ : R →+* R') (Y : Over (Spec (.of R'))) [IsReduced Y.left]
    (A : PEL.Has.IntegralPELObject P R' (φ.comp iotaO) N Y) :
    ∃! f : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X,
      Nonempty (PEL.Iso.PolarizedActionIso ((U.baseChange φ).pullback f).data A.data) := by
  let e := (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom φ))).homEquiv Y X
  have : IsReduced (PEL.ScalarRestriction.coefficientRestriction φ Y).left := inferInstanceAs (IsReduced Y.left)
  obtain ⟨f, hf, hu⟩ := hU (PEL.ScalarRestriction.coefficientRestriction φ Y) (A.restrictScalars φ Y)
  refine ⟨e f, ?_, ?_⟩
  · apply (integralPEL_action_baseChange_classifying_iff φ U Y A (e f)).mpr
    simpa only [e, Equiv.symm_apply_apply] using hf
  · intro g hg
    have h := hu (e.symm g) ((integralPEL_action_baseChange_classifying_iff φ U Y A g).mp hg)
    exact e.symm.injective (h.trans (e.symm_apply_apply f).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FineBaseChange
