import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELParameterUniqueness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FixedComparison

/-! # PEL Parameter Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELParameterClassification

noncomputable section

/-! Every integral PEL family has a unique classifier over the actual
fine pure model, with its full native polarized action comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FixedComparison

theorem relativePELParameter_classifies
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [CharZero K] [Countable K] {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* K)
    (M : Pure.Fine.PurePolarizedModel (3 * s) P.polarizationType N (Spec (.of K)))
    [LocallyOfFiniteType M.space.hom] (hM : M.IsFine) (hN : 3 ≤ N)
    {Z : Over M.space.left} (u : (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M.space M.universal).obj (op Z))
    (hclass : ∀ V : Over M.space.left, Function.Bijective
      (fun f : V ⟶ Z => (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M.space M.universal).map f.op u))
    (T : Over (Spec (.of K))) (B : PELModuli.IntegralModel.PEL.Has.IntegralPELObject P K iotaO N T) :
    ∃! j : T ⟶ (Over.map M.space.hom).obj Z, Nonempty
      (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso ((PELModuli.IntegralModel.Relative.FamilyClassification.relativePELUniversal P iotaO M.space M.universal Z u).data.pullback j.left) B.data) := by
  obtain ⟨f, ⟨e⟩, _⟩ := hM T B.data.polarized
  let t : Over M.space.left := Over.mk f.left
  let b : (Over.map M.space.hom).obj t ⟶ T := Over.homMk (𝟙 T.left)
    ((Category.id_comp _).trans f.w.symm)
  let B' := B.pullback b
  let e' : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback t.hom) B'.data.polarized :=
    e.trans (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId B.data.polarized).symm
  obtain ⟨c, ec, _⟩ := PELModuli.IntegralModel.Relative.FixedComparison.relativePELUniversal_classifying_with_comparison P iotaO M.space M.universal
    u (hclass t).surjective B' e'
  let k : T ⟶ (Over.map M.space.hom).obj Z := Over.homMk c.left
    ((Category.assoc c.left Z.hom M.space.hom).symm.trans
      ((congrArg (fun z => z ≫ M.space.hom) c.w).trans f.w))
  let ek : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso ((PELModuli.IntegralModel.Relative.FamilyClassification.relativePELUniversal P iotaO M.space M.universal Z u).data.pullback k.left) B.data :=
    ec.trans (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackId B.data)
  refine ⟨k, ⟨ek⟩, ?_⟩
  rintro j ⟨ej⟩
  exact PELParameterUniqueness.relativePELParameter_classifying_unique P iotaO M hM hN u
    (fun V => (hclass V).injective) T B j k ej ek

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELParameterClassification
