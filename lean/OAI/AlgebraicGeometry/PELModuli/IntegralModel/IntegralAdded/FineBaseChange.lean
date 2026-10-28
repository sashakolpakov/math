import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.ScalarChange

/-! # Fine Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineBaseChange

noncomputable section

section

/-! A two-level fine classifier on the principal open of one coefficient
becomes an actual fine classifier after any coefficient-ring map making
that element a unit. The universal family is the actual base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}

theorem integralAddedPEL_fine_baseChange_of_unit
    (U : PELId.IntegralAddedPELLevel P R iotaO L N X) (r : R)
    (hclass : ∀ (T : Over (Spec (.of R))) [IsReduced T.left],
      (∀ x : T.left, r ∉ (T.hom x).asIdeal) →
      ∀ A : PELId.IntegralAddedPELLevel P R iotaO L N T,
        ∃! f : T ⟶ X, Nonempty (PELId.IntegralAddedPELLevel.Iso (U.pullback f) A))
    (φ : R →+* R') (hr : IsUnit (φ r))
    (Y : Over (Spec (.of R'))) [IsReduced Y.left]
    (A : PELId.IntegralAddedPELLevel P R' (φ.comp iotaO) L N Y) :
    ∃! f : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X,
      Nonempty (PELId.IntegralAddedPELLevel.Iso ((U.baseChange φ).pullback f) A) := by
  let e := (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom φ))).homEquiv Y X
  have : IsReduced (PEL.ScalarRestriction.coefficientRestriction φ Y).left := inferInstanceAs (IsReduced Y.left)
  have hunit (x : (PEL.ScalarRestriction.coefficientRestriction φ Y).left) :
      r ∉ ((PEL.ScalarRestriction.coefficientRestriction φ Y).hom x).asIdeal := by
    intro hx
    have hx' : φ r ∈ (Y.hom x).asIdeal := hx
    exact (Y.hom x).isPrime.ne_top ((Y.hom x).asIdeal.eq_top_of_isUnit_mem hx' hr)
  obtain ⟨f, hf, hu⟩ := hclass (PEL.ScalarRestriction.coefficientRestriction φ Y) hunit (A.restrictScalars φ Y)
  refine ⟨e f, ?_, ?_⟩
  · apply (ScalarChange.integralAddedPEL_baseChange_classifying_iff φ U Y A (e f)).mpr
    simpa only [e, Equiv.symm_apply_apply] using hf
  · intro g hg
    have h := hu (e.symm g) ((ScalarChange.integralAddedPEL_baseChange_classifying_iff φ U Y A g).mp hg)
    exact e.symm.injective (h.trans (e.symm_apply_apply f).symm)

end

/-! Fine two-level classification is preserved by arbitrary coefficient
change, with the actual base-changed universal family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}

theorem integralAddedPEL_fine_baseChange
    (U : PELId.IntegralAddedPELLevel P R iotaO L N X)
    (hclass : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (A : PELId.IntegralAddedPELLevel P R iotaO L N T),
      ∃! f : T ⟶ X, Nonempty (PELId.IntegralAddedPELLevel.Iso (U.pullback f) A))
    (φ : R →+* R') (Y : Over (Spec (.of R'))) [IsReduced Y.left]
    (A : PELId.IntegralAddedPELLevel P R' (φ.comp iotaO) L N Y) :
    ∃! f : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X,
      Nonempty (PELId.IntegralAddedPELLevel.Iso ((U.baseChange φ).pullback f) A) :=
  integralAddedPEL_fine_baseChange_of_unit U 1 (fun T _ _ B => hclass T B)
    φ (by rw [map_one]; exact isUnit_one) Y A

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineBaseChange
