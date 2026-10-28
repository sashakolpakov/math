import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.Reconstruction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.LevelReplacement

/-! # Fine Swap -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded

/-! Interchange the two actual full markings of an integral PEL object.
The operation preserves the underlying group, polarization and action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {T U : Over (Spec (.of R))}

def PELId.IntegralAddedPELLevel.swap (A : PELId.IntegralAddedPELLevel P R iotaO L N T) :
    PELId.IntegralAddedPELLevel P R iotaO N L T where
  auxiliary := A.forgetAuxiliary
  prescribed := A.auxiliary.data.polarized.level

@[simp] theorem PELId.IntegralAddedPELLevel.swap_swap (A : PELId.IntegralAddedPELLevel P R iotaO L N T) : A.swap.swap = A := rfl

theorem PELId.IntegralAddedPELLevel.swap_pullback (A : PELId.IntegralAddedPELLevel P R iotaO L N T) (f : U ⟶ T) :
    (A.pullback f).swap = A.swap.pullback f := rfl

def PELId.IntegralAddedPELLevel.Iso.swap {A B : PELId.IntegralAddedPELLevel P R iotaO L N T} (e : PELId.IntegralAddedPELLevel.Iso A B) :
    PELId.IntegralAddedPELLevel.Iso A.swap B.swap where
  auxiliary := e.forgetAuxiliary
  prescribed := by
    apply AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
    exact e.auxiliary.polarized.level

end AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded

namespace AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineSwap

/-! Fine classification is unchanged when the two actual markings
are interchanged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}

theorem integralAddedPEL_fine_swap (U : PELId.IntegralAddedPELLevel P R iotaO L N X)
    (hU : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (A : PELId.IntegralAddedPELLevel P R iotaO L N T),
      ∃! f : T ⟶ X, Nonempty (PELId.IntegralAddedPELLevel.Iso (U.pullback f) A))
    (T : Over (Spec (.of R))) [IsReduced T.left]
    (A : PELId.IntegralAddedPELLevel P R iotaO N L T) :
    ∃! f : T ⟶ X, Nonempty (PELId.IntegralAddedPELLevel.Iso (U.swap.pullback f) A) := by
  obtain ⟨f, ⟨e⟩, hu⟩ := hU T A.swap
  refine ⟨f, ⟨e.swap⟩, ?_⟩
  rintro g ⟨a⟩
  exact hu g ⟨a.swap⟩

end AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineSwap

end

end OAI
