import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.ScalarRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.Iff

/-! # Generic -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.Generic

noncomputable section

section

/-! The universal PEL family on the base change of the actual reduced
characteristic-zero model. Its classifying predicate is exactly the one
used by IntegralPELSpread on reduced test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {R R' : Type} [CommRing R] [CommRing R']
  {iotaO : NumberField.RingOfIntegers E →+* R}
  (φ : R →+* R') (X : Over (Spec (.of R)))

/-- Exact family classification commutes with change of coefficient ring,
through the actual map/pullback adjunction and Poincare-compatible family
isomorphisms. -/
theorem integralPEL_baseChange_classifying_iff
    (U : PEL.Has.IntegralPELObject P R iotaO N X) (Y : Over (Spec (.of R')))
    (A : PEL.Has.IntegralPELObject P R' (φ.comp iotaO) N Y)
    (f : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X) :
    Nonempty (PEL.Has.PulledBackPELDataIso (U.baseChange φ).data A.data f.left (𝟙 Y.left)) ↔
      Nonempty (PEL.Has.PulledBackPELDataIso U.data (A.restrictScalars φ Y).data
        ((((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom φ))).homEquiv Y X).symm f).left)
        (𝟙 Y.left)) := by
  let q := pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))
  constructor
  · rintro ⟨e⟩
    exact ⟨PEL.Has.PulledBackPELDataIso.ofActionIso
      ((PEL.Iso.PolarizedActionIso.pullbackComp U.data q f.left).symm.trans e.toActionIso)⟩
  · rintro ⟨e⟩
    exact ⟨PEL.Has.PulledBackPELDataIso.ofActionIso
      ((PEL.Iso.PolarizedActionIso.pullbackComp U.data q f.left).trans e.toActionIso)⟩

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  {iota : E →+* K} (j : K →+* L) (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)

/-- The actual universal object on the generic comparison space of IntegralModel. -/
abbrev reducedGenericPELUniversal :
    PEL.Has.IntegralPELObject P L
      (j.comp (iota.comp (algebraMap (NumberField.RingOfIntegers E) E))) N
      ((Over.pullback (Spec.map (CommRingCat.ofHom j))).obj (Reduction.reduction M.space)) :=
  (Iff.reducedPELUniversal M).baseChange j

omit [NumberField L] in
/-- Every reduced test scheme over the extended number field has a unique
classifying map to the base change of the original reduced model. The
universal-family comparison preserves action, polarization, Poincare class,
and full level. -/
theorem reduced_generic_finePEL_classifies (hM : M.IsFine)
    (Y : Over (Spec (.of L))) [IsReduced Y.left]
    (A : PEL.Has.IntegralPELObject P L
      (j.comp (iota.comp (algebraMap (NumberField.RingOfIntegers E) E))) N Y) :
    ∃! f : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom j))).obj (Reduction.reduction M.space),
      Nonempty (PEL.Has.PulledBackPELDataIso (reducedGenericPELUniversal j M).data A.data
        f.left (𝟙 Y.left)) := by
  let e := (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom j))).homEquiv Y (Reduction.reduction M.space)
  have : IsReduced (PEL.ScalarRestriction.coefficientRestriction j Y).left := inferInstanceAs (IsReduced Y.left)
  obtain ⟨f, hf, huniq⟩ := Iff.reduced_finePEL_classifies M hM
    (PEL.ScalarRestriction.coefficientRestriction j Y) (A.restrictScalars j Y)
  refine ⟨e f, ?_, ?_⟩
  · apply (integralPEL_baseChange_classifying_iff j (Reduction.reduction M.space)
      (Iff.reducedPELUniversal M) Y A (e f)).mpr
    have hf' : Nonempty (PEL.Has.PulledBackPELDataIso (Iff.reducedPELUniversal M).data
        (A.restrictScalars j Y).data f.left (𝟙 Y.left)) := hf
    simpa only [e, Equiv.symm_apply_apply] using hf'
  · intro g hg
    have h := huniq (e.symm g) ((integralPEL_baseChange_classifying_iff j (Reduction.reduction M.space)
      (Iff.reducedPELUniversal M) Y A g).mp hg)
    exact e.symm.injective (h.trans (e.symm_apply_apply f).symm)

end

/-! The given ReferenceFamily universal family classifies reduced generic PEL
objects through actual polarized action isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    {iota : E →+* K} (j : K →+* L) (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)

omit [NumberField L] in
theorem reduced_generic_finePEL_action_classifies (hM : M.IsFine)
    (Y : Over (Spec (.of L))) [IsReduced Y.left]
    (A : PEL.Has.IntegralPELObject P L
      (j.comp (iota.comp (algebraMap (NumberField.RingOfIntegers E) E))) N Y) :
    ∃! f : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom j))).obj (Reduction.reduction M.space),
      Nonempty (PEL.Iso.PolarizedActionIso ((reducedGenericPELUniversal j M).pullback f).data A.data) := by
  obtain ⟨f, ⟨e⟩, hu⟩ := reduced_generic_finePEL_classifies j M hM Y A
  refine ⟨f, ⟨e.toActionIso.trans (PEL.Iso.PolarizedActionIso.pullbackId A.data)⟩, ?_⟩
  rintro g ⟨a⟩
  exact hu g ⟨PEL.Has.PulledBackPELDataIso.ofActionIso
    (a.trans (PEL.Iso.PolarizedActionIso.pullbackId A.data).symm)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.Generic
