import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.QuotientFibers
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.ScalarChange

/-! # Quotient Scalar Fibers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.QuotientScalarFibers.IntegralAuxiliaryAction

noncomputable section

/-! The actual quotient-fiber classification commutes with every change
of coefficient ring, using restriction of scalars on reduced tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s L N : ℕ} [NeZero L]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem scalar_quotient_eq_iff_prescribed_iso (π : X ⟶ Q)
    (hk : IsKernelPair π.left (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (ActionSpace.IntegralAuxiliaryAction.target U hU).left)
    (φ : R →+* R') (T : Over (Spec (.of R'))) [IsReduced T.left]
    (f g : T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X) :
    f ≫ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).map π =
      g ≫ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).map π ↔
      Nonempty (PEL.Iso.PolarizedActionIso ((U.baseChange φ).forgetAuxiliary.pullback f).data
        ((U.baseChange φ).forgetAuxiliary.pullback g).data) := by
  let b := Spec.map (CommRingCat.ofHom φ)
  let adj := Over.mapPullbackAdj b
  let f₀ := (adj.homEquiv T X).symm f
  let g₀ := (adj.homEquiv T X).symm g
  have : IsReduced (PEL.ScalarRestriction.coefficientRestriction φ T).left := inferInstanceAs (IsReduced T.left)
  have heq : f ≫ (Over.pullback b).map π = g ≫ (Over.pullback b).map π ↔
      f₀ ≫ π = g₀ ≫ π := by
    rw [← (adj.homEquiv T Q).symm.injective.eq_iff]
    rw [adj.homEquiv_naturality_right_symm, adj.homEquiv_naturality_right_symm]
  let ef : PEL.Iso.PolarizedActionIso ((U.baseChange φ).forgetAuxiliary.pullback f).data
      (U.forgetAuxiliary.pullback f₀).data :=
    PEL.Iso.PolarizedActionIso.pullbackComp U.forgetAuxiliary.data (pullback.fst X.hom b) f.left
  let eg : PEL.Iso.PolarizedActionIso ((U.baseChange φ).forgetAuxiliary.pullback g).data
      (U.forgetAuxiliary.pullback g₀).data :=
    PEL.Iso.PolarizedActionIso.pullbackComp U.forgetAuxiliary.data (pullback.fst X.hom b) g.left
  rw [heq, QuotientFibers.IntegralAuxiliaryAction.quotient_eq_iff_prescribed_iso U hU π hk f₀ g₀]
  constructor
  · rintro ⟨e⟩
    exact ⟨ef.trans (e.trans eg.symm)⟩
  · rintro ⟨e⟩
    exact ⟨ef.symm.trans (e.trans eg)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.QuotientScalarFibers.IntegralAuxiliaryAction
