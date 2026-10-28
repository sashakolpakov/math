import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying

/-! # PEL Double Pullback Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Fineness detects equality of the actual classifying maps, including
comparison with a family pulled back through a reduced test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine)
    {T S : Over (Spec (.of K))}

include hM in
theorem Models.FinePELModel.universal_pullback_class_injective {f g : T ⟶ M.space}
    (h : (M.universal.pullback f).classOf = (M.universal.pullback g).classOf) : f = g := by
  obtain ⟨q, _, hu⟩ := hM T (M.universal.pullback f)
  exact (hu f ⟨Models.PELPullbackIso.canonical M.universal f⟩).trans
    (hu g ((Models.PELPullbackIso.nonempty_iff_classOf g).mpr h)).symm

theorem Models.FinePELModel.universal_doublePullback_class (f : T ⟶ M.space) (r : S ⟶ T) (p : T ⟶ S) :
    (((M.universal.pullback f).pullback r).pullback p).classOf =
      (M.universal.pullback (p ≫ r ≫ f)).classOf := by
  apply Quotient.sound
  exact ⟨((PEL.Objects.PELIso.pullbackComp M.universal (r ≫ f) p).trans
    ((PEL.Objects.PELIso.pullbackComp M.universal f r).pullback p)).symm⟩

include hM in
theorem Models.FinePELModel.universal_class_eq_doublePullback_iff (f : T ⟶ M.space) (r : S ⟶ T) (p : T ⟶ S) :
    (M.universal.pullback f).classOf = (((M.universal.pullback f).pullback r).pullback p).classOf ↔
      f = p ≫ r ≫ f := by
  rw [M.universal_doublePullback_class f r p]
  exact ⟨M.universal_pullback_class_injective hM, fun h => congrArg (fun q => (M.universal.pullback q).classOf) h⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
