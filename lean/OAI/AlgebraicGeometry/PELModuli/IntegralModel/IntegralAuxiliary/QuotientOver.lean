import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Quotient
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.CoverType

/-! # Quotient Over -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.QuotientOver.IntegralAuxiliaryAction

noncomputable section

/-! The actual auxiliary quotient lives over the same coefficient
ring. Its reducedness, finite type and noetherianity follow from the
constructed finite etale cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [IsNoetherianRing R] {s L N : ℕ} [NeZero L]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iotaO : NumberField.RingOfIntegers E →+* R}
    {X : Over (Spec (.of R))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem exists_quotient_over (hrigid : U.PrescribedRigid)
    (hOrbit : ∀ x : X.left, ∃ V : X.left.Opens, IsAffineOpen V ∧
      ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (ActionSpace.IntegralAuxiliaryAction.target U hU).left x y → y ∈ V) :
    ∃ (Q : Over (Spec (.of R))) (π : X ⟶ Q), IsReduced Q.left ∧ IsNoetherian Q.left ∧
      LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧
      IsFinite π.left ∧ Etale π.left ∧ Surjective π.left ∧
      IsKernelPair π.left (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (ActionSpace.IntegralAuxiliaryAction.target U hU).left ∧
      ∀ (T : Over (Spec (.of R))) (f : X ⟶ T),
        ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L ≫ f = ActionSpace.IntegralAuxiliaryAction.target U hU ≫ f → ∃! q : Q ⟶ T, π ≫ q = f := by
  obtain ⟨Q, π, hr, hf, he, hs, hk, hquot⟩ := Quotient.IntegralAuxiliaryAction.exists_quotient_scheme U hU hrigid hOrbit
  have : IsFinite π := hf
  have : Etale π := he
  have : Surjective π := hs
  obtain ⟨b, hb, _⟩ := hquot (Spec (.of R)) X.hom
    ((ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).w.trans (ActionSpace.IntegralAuxiliaryAction.target U hU).w.symm)
  let Q' : Over (Spec (.of R)) := Over.mk b
  let p : X ⟶ Q' := Over.homMk π hb
  have : IsFinite p.left := hf
  have : Flat p.left := inferInstanceAs (Flat π)
  have : Surjective p.left := hs
  obtain ⟨hft, hqc, hn⟩ := Finite.CoverType.finite_flat_cover_noetherian p
  refine ⟨Q', p, hr, hn, hft, hqc, hf, he, hs, hk, ?_⟩
  intro T f hinv
  obtain ⟨q, hq, hu⟩ := hquot T.left f.left (congrArg Over.Hom.left hinv)
  have hbase : q ≫ T.hom = b := by
    apply (cancel_epi π).mp
    rw [← Category.assoc, hq, f.w, hb]
  let q' : Q' ⟶ T := Over.homMk q hbase
  refine ⟨q', Over.OverMorphism.ext hq, ?_⟩
  intro a ha
  exact Over.OverMorphism.ext (hu a.left (congrArg Over.Hom.left ha))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.QuotientOver.IntegralAuxiliaryAction
