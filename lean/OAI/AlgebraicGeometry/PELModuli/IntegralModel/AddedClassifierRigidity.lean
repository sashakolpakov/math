import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CharacteristicZeroPolarizedRigidity

/-! # Added Classifier Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AddedClassifierRigidity

noncomputable section

/-! A two-level classifier transfers prescribed-level rigidity from
the actual bounded universal family to every classified PEL object. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {V T : Over (Spec (.of R))}

theorem addedPEL_classifier_prescribed_rigidity
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N V)
    (A : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N T)
    (hclass : ∃ f : T ⟶ V, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback f) A))
    (hRigid : ∀ (f : T ⟶ V)
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (U.forgetAuxiliary.data.polarized.pullback f.left)
        (U.forgetAuxiliary.data.polarized.pullback f.left)),
      e.abelian.hom = 𝟙 (U.forgetAuxiliary.data.polarized.abelian.pullback f.left).scheme)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A.forgetAuxiliary.data.polarized A.forgetAuxiliary.data.polarized) :
    e.abelian.hom = 𝟙 A.forgetAuxiliary.data.polarized.abelian.scheme := by
  obtain ⟨f, ⟨a⟩⟩ := hclass
  exact AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent.pure_abelian_eq_id_via e a.forgetAuxiliary.polarized.symm (hRigid f)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AddedClassifierRigidity
