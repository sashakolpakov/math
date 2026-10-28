import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.RelativeRelabelMaps

/-! # Freeness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Prescribed-level rigidity forces any auxiliary label fixing an
actual reduced family to be the identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}

theorem IntegralAdded.PELId.IntegralAddedPELLevel.relabel_eq_one_of_abelian_id (A : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)
    (b : LocallyConstant X.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L))
    (e : IntegralAdded.PELId.IntegralAddedPELLevel.Iso (A.relabelAuxiliary b) A)
    (he : e.auxiliary.polarized.abelian.hom = 𝟙 A.auxiliary.data.polarized.abelian.scheme) : b = 1 := by
  have hlevel : AbelianModuli.ReferenceFamily.Level.IsoCalculus.relabelFullLevel A.auxiliary.data.polarized.level b =
      A.auxiliary.data.polarized.level := by
    apply AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
    intro T c
    have h := e.auxiliary.polarized.level T c
    rw [he] at h
    exact (Category.comp_id
      (((AbelianModuli.ReferenceFamily.Level.IsoCalculus.relabelFullLevel A.auxiliary.data.polarized.level b).hom.app (.op T) c).val)).symm.trans h
  apply A.auxiliary.data.polarized.level.labelsEquiv.symm.injective
  exact hlevel.trans (AbelianModuli.ReferenceFamily.Level.IsoCalculus.relabelFullLevel_one A.auxiliary.data.polarized.level).symm

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedRigid (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) : Prop :=
  ∀ (T : Over (Spec (.of R))) [IsReduced T.left] (f : T ⟶ X)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (U.forgetAuxiliary.pullback f).data.polarized
      (U.forgetAuxiliary.pullback f).data.polarized),
    e.abelian.hom = 𝟙 (U.forgetAuxiliary.pullback f).data.polarized.abelian.scheme

theorem IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelAt_fixed (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)
    (hU : U.IsFine) (hrigid : U.PrescribedRigid)
    {T : Over (Spec (.of R))} [IsReduced T.left] (f : T ⟶ X)
    (b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L))
    (hf : U.auxiliaryRelabelAt hU f b = f) : b = 1 := by
  let e : IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((U.pullback f).relabelAuxiliary b) (U.pullback f) :=
    (U.auxiliaryRelabelAtComparison hU f b).symm.trans (U.pullbackCongrIso _ _ hf)
  exact IntegralAdded.PELId.IntegralAddedPELLevel.relabel_eq_one_of_abelian_id (U.pullback f) b e
    (hrigid T f e.forgetAuxiliary.polarized)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelAt_injective (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)
    (hU : U.IsFine) (hrigid : U.PrescribedRigid)
    {T : Over (Spec (.of R))} [IsReduced T.left] (f : T ⟶ X) :
    Function.Injective (U.auxiliaryRelabelAt hU f) := by
  intro b c h
  have he : U.auxiliaryRelabelAt hU f (b * c⁻¹) = f := by
    rw [← U.auxiliaryRelabelAt_mul hU, h, U.auxiliaryRelabelAt_mul hU,
      mul_inv_cancel, U.auxiliaryRelabelAt_one hU]
  exact mul_inv_eq_one.mp (U.auxiliaryRelabelAt_fixed hU hrigid f _ he)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
