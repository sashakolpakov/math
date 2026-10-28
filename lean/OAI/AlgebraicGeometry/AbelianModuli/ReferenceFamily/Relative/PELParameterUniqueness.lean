import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldRelativePELAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.PullbackIsoUniqueness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FamilyUniqueness

/-! # PEL Parameter Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELParameterUniqueness

noncomputable section

/-! The represented integral action has a unique global classifier over
the fine prescribed-level pure model, on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FamilyUniqueness

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [CharZero K] [Countable K] {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* K)
    (M : Pure.Fine.PurePolarizedModel (3 * s) P.polarizationType N (Spec (.of K)))
    [LocallyOfFiniteType M.space.hom] (hM : M.IsFine) (hN : 3 ≤ N)

def relativePELParameterForget (Z : Over M.space.left) : (Over.map M.space.hom).obj Z ⟶ M.space :=
  Over.homMk Z.hom rfl

include hM hN in
theorem relativePELParameter_classifying_unique {Z : Over M.space.left}
    (u : (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M.space M.universal).obj (op Z))
    (hclass : ∀ V : Over M.space.left, Function.Injective
      (fun f : V ⟶ Z => (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M.space M.universal).map f.op u))
    (T : Over (Spec (.of K))) (B : PELModuli.IntegralModel.PEL.Has.IntegralPELObject P K iotaO N T)
    (j k : T ⟶ (Over.map M.space.hom).obj Z)
    (a : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso ((PELModuli.IntegralModel.Relative.FamilyClassification.relativePELUniversal P iotaO M.space M.universal Z u).data.pullback j.left) B.data)
    (b : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso ((PELModuli.IntegralModel.Relative.FamilyClassification.relativePELUniversal P iotaO M.space M.universal Z u).data.pullback k.left) B.data) : j = k := by
  let f := j ≫ relativePELParameterForget P M Z
  let h := k ≫ relativePELParameterForget P M Z
  let aj : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback f.left) B.data.polarized :=
    (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp M.universal Z.hom j.left).symm.trans a.polarized
  let bk : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback h.left) B.data.polarized :=
    (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp M.universal Z.hom k.left).symm.trans b.polarized
  obtain ⟨_, _, hu⟩ := hM T B.data.polarized
  have hh : h = f := (hu h ⟨bk⟩).trans (hu f ⟨aj⟩).symm
  let V : Over M.space.left := Over.mk f.left
  let q : V ⟶ Z := Over.homMk j.left rfl
  let r : V ⟶ Z := Over.homMk k.left (congrArg Over.Hom.left hh)
  have he : r = q := PELModuli.IntegralModel.Relative.FamilyUniqueness.relativePELUniversal_classifying_unique P iotaO M.space M.universal u
    (hclass V) (fun e => Pure.PullbackRigidity.purePullback_abelian_eq_id M.space.hom M.universal hN f.left e)
    r q (b.trans a.symm)
  exact Over.OverMorphism.ext (congrArg (fun v : V ⟶ Z => v.left) he).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELParameterUniqueness
