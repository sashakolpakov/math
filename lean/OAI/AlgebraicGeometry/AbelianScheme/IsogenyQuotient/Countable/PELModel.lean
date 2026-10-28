import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.PolarizedLevelModel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedActionDescent
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RecoveredPELConditions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying

/-! # PEL Model -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.PELModel.Construction

noncomputable section

/-! Every original geometric PEL object at nonzero level is defined
over an actual countable algebraically closed subfield. The model
retains the prescribed number-field embedding, full native polarization,
ordered level, every integral action coefficient, Rosati compatibility,
and the original Lie ranks on all geometric tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying

set_option backward.isDefEq.respectTransparency false in
theorem countable_full_PEL_model_exists
    {E K k : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] [Field k] [CharZero k] [IsAlgClosed k]
    {s N : ℕ} [NeZero N] (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (iota : E →+* K) (j : K →+* k)
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom j)))) :
    ∃ (F : Subfield k) (jF : K →+* F), Countable F ∧ IsAlgClosed F ∧ F.subtype.comp jF = j ∧
      ∃ B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom jF))),
      ∃ q : Over.mk (Spec.map (CommRingCat.ofHom j)) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom jF)),
        q.left = Spec.map (CommRingCat.ofHom F.subtype) ∧ Nonempty (AbelianModuli.ReferenceFamily.Models.PELPullbackIso B A q) := by
  obtain ⟨M⟩ := PolarizedLevelModel.Construction.countable_polarized_full_level_model_exists A.polarized
  let F := M.field
  let jF := CoefficientFields.Construction.numberFieldToAlgebraicallyClosedSubfield F j
  have hjF : F.subtype.comp jF = j := CoefficientFields.Construction.numberFieldToAlgebraicallyClosedSubfield_comp F j
  let T : Over (Spec (.of K)) := Over.mk (Spec.map (CommRingCat.ofHom j))
  let U : Over (Spec (.of K)) := Over.mk (Spec.map (CommRingCat.ofHom jF))
  let u := Spec.map (CommRingCat.ofHom F.subtype)
  let q : T ⟶ U := Over.homMk u (by
    change Spec.map (CommRingCat.ofHom F.subtype) ≫ Spec.map (CommRingCat.ofHom jF) =
      Spec.map (CommRingCat.ofHom j)
    rw [← Spec.map_comp]
    exact congrArg (fun r : K →+* k => Spec.map (CommRingCat.ofHom r)) hjF)
  obtain ⟨σ, hσ⟩ := AlgebraicallyClosedActionDescent.Construction.algebraicallyClosed_action_of_recovery F k M.polarized.abelian
    A.polarized.abelian M.recovery.abelian A.action
  have hRosati : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation M.polarized σ :=
    RecoveredPELConditions.Construction.rosati_of_recovered_field_action F k A.polarized M.polarized M.recovery A.action σ hσ A.rosati
  let iotaO := iota.comp (algebraMap (NumberField.RingOfIntegers E) E)
  have : Surjective q.left :=
    (show Surjective u from ⟨Function.surjective_to_subsingleton _⟩)
  have : IsLocallyNoetherian U.left := inferInstanceAs (IsLocallyNoetherian (Spec (.of F)))
  let B₀ : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) U.left := M.polarized.abelian
  let σ₀ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B₀ := σ
  let e₀ : A.polarized.abelian.scheme ≅ (B₀.pullback q.left).scheme := M.recovery.abelian
  have : CategoryTheory.IsMonHom e₀.hom := M.recovery.abelianGroup
  have hσ₀ : ∀ a, A.action.map a ≫ e₀.hom = e₀.hom ≫ (Over.pullback q.left).map (σ₀.map a) := hσ
  have hLie := RecoveredPELConditions.Construction.integralLieRanks_of_recovered_surjective_action (M := U) (T := T) P iotaO
    A.polarized.abelian B₀ A.action σ₀ q e₀ hσ₀ A.lieRanks
  let B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N U := {
    polarized := M.polarized
    action := σ
    rosati := hRosati
    lieRanks := hLie }
  let e : AbelianModuli.ReferenceFamily.PEL.Objects.PELIso A (B.pullback q) := ⟨M.recovery, hσ⟩
  exact ⟨F, jF, inferInstance, inferInstance, hjF, B, q, rfl, ⟨AbelianModuli.ReferenceFamily.Models.PELPullbackIso.ofPELIso e⟩⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.PELModel.Construction
