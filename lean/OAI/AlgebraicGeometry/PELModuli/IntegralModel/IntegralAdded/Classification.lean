import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId

/-! # Classification -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded

noncomputable section

section

/-! Actual two-level PEL pullback comparisons for composition and
equality of parameter maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {T U V : Over (Spec (.of R))}

def PELId.IntegralAddedPELLevel.pullbackCompIso (A : PELId.IntegralAddedPELLevel P R iotaO L N T) (f : U ⟶ T) (h : V ⟶ U) :
    PELId.IntegralAddedPELLevel.Iso ((A.pullback f).pullback h) (A.pullback (h ≫ f)) where
  auxiliary := PEL.Iso.PolarizedActionIso.pullbackComp A.auxiliary.data f.left h.left
  prescribed := (AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.pullbackCompIso A.pure f.left h.left).prescribed

def PELId.IntegralAddedPELLevel.pullbackCongrIso (A : PELId.IntegralAddedPELLevel P R iotaO L N T)
    (f h : U ⟶ T) (w : f = h) : PELId.IntegralAddedPELLevel.Iso (A.pullback f) (A.pullback h) := by
  subst h
  exact PELId.IntegralAddedPELLevel.Iso.refl _

end

/-! A compact interface for the already constructed two-level fine
classification on reduced tests, retaining actual comparison maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}

def PELId.IntegralAddedPELLevel.IsFine (U : PELId.IntegralAddedPELLevel P R iotaO L N X) : Prop :=
  ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
    (A : PELId.IntegralAddedPELLevel P R iotaO L N T),
    ∃! f : T ⟶ X, Nonempty (PELId.IntegralAddedPELLevel.Iso (U.pullback f) A)

def PELId.IntegralAddedPELLevel.classifyingMap (U : PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (T : Over (Spec (.of R))) [IsReduced T.left]
    (A : PELId.IntegralAddedPELLevel P R iotaO L N T) : T ⟶ X := (hU T A).choose

def PELId.IntegralAddedPELLevel.classifyingIso (U : PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (T : Over (Spec (.of R))) [IsReduced T.left]
    (A : PELId.IntegralAddedPELLevel P R iotaO L N T) :
    PELId.IntegralAddedPELLevel.Iso (U.pullback (U.classifyingMap hU T A)) A :=
  Classical.choice (hU T A).choose_spec.1

theorem PELId.IntegralAddedPELLevel.classifying_unique (U : PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (T : Over (Spec (.of R))) [IsReduced T.left]
    (A : PELId.IntegralAddedPELLevel P R iotaO L N T) (f : T ⟶ X)
    (e : PELId.IntegralAddedPELLevel.Iso (U.pullback f) A) : f = U.classifyingMap hU T A :=
  (hU T A).choose_spec.2 f ⟨e⟩

def PELId.IntegralAddedPELLevel.Iso.ofEq {A B : PELId.IntegralAddedPELLevel P R iotaO L N X} (h : A = B) : PELId.IntegralAddedPELLevel.Iso A B :=
  h ▸ PELId.IntegralAddedPELLevel.Iso.refl A

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded
