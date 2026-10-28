import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.FiberRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.QuotientOver

/-! # Quotient Fibers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.QuotientFibers.IntegralAuxiliaryAction

noncomputable section

/-! The constructed quotient identifies precisely the isomorphism classes
of the actual prescribed PEL families on every reduced test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X T Q : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem homRelation_iff_prescribed_iso [IsReduced T.left] (f g : T ⟶ X) :
    AbelianModuli.ReferenceFamily.RepresentedRelations.homRelation (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L) (ActionSpace.IntegralAuxiliaryAction.target U hU) f g ↔
      Nonempty (PEL.Iso.PolarizedActionIso (U.forgetAuxiliary.pullback f).data
        (U.forgetAuxiliary.pullback g).data) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := (ActionPoints.IntegralAuxiliaryAction.homRelation_iff U hU f g).mp h
    exact ⟨(U.auxiliaryRelabelAtComparison hU f b).forgetAuxiliary.symm.trans
      (U.pullbackCongrIso _ _ hb).forgetAuxiliary⟩
  · rintro ⟨e⟩
    obtain ⟨b, ⟨eb⟩⟩ := IntegralAdded.PELId.IntegralAddedPELLevel.exists_relabel_of_prescribed_iso
      (U.pullback f) (U.pullback g) e
    apply (ActionPoints.IntegralAuxiliaryAction.homRelation_iff U hU f g).mpr
    refine ⟨b, ?_⟩
    have h1 := U.classifying_unique hU T (U.pullback g) (U.auxiliaryRelabelAt hU f b)
      ((U.auxiliaryRelabelAtComparison hU f b).trans eb)
    have h2 := U.classifying_unique hU T (U.pullback g) g (IntegralAdded.PELId.IntegralAddedPELLevel.Iso.refl _)
    exact h1.trans h2.symm

theorem quotient_eq_iff_prescribed_iso (π : X ⟶ Q)
    (hk : IsKernelPair π.left (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (ActionSpace.IntegralAuxiliaryAction.target U hU).left)
    [IsReduced T.left] (f g : T ⟶ X) :
    f ≫ π = g ≫ π ↔
      Nonempty (PEL.Iso.PolarizedActionIso (U.forgetAuxiliary.pullback f).data
        (U.forgetAuxiliary.pullback g).data) := by
  rw [← homRelation_iff_prescribed_iso U hU f g]
  constructor
  · intro h
    let r := hk.lift f.left g.left (congrArg Over.Hom.left h)
    have hr : r ≫ (ActionSpace.IntegralAuxiliaryAction.relation X (3 * s) L).hom = T.hom := by
      rw [← (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).w, ← Category.assoc, hk.lift_fst]
      exact f.w
    exact ⟨Over.homMk r hr, Over.OverMorphism.ext (hk.lift_fst _ _ _),
      Over.OverMorphism.ext (hk.lift_snd _ _ _)⟩
  · rintro ⟨r, hr, hs⟩
    apply Over.OverMorphism.ext
    have h := congrArg (fun a => r.left ≫ a) hk.w
    simpa only [← Category.assoc, ← Over.comp_left, hr, hs] using h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.QuotientFibers.IntegralAuxiliaryAction
