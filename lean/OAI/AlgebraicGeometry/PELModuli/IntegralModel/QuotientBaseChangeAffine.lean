import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AuxiliaryAffineNeighborhoodDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.KernelPair
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CharacteristicZeroPrescribedRigidity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.FamilyComparisonBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth

/-! # Quotient Base Change Affine -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuotientBaseChangeAffine

noncomputable section

/-! Affine neighborhoods descend to the actual prescribed-level
reference after any field extension of the arithmetic coefficient field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K K' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [CharZero K] [Countable K] [Field K'] {s L N : ℕ} [NeZero L]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iotaO : NumberField.RingOfIntegers E →+* K}
    {X Y : Over (Spec (.of K))} [IsNoetherian X.left] [LocallyOfFiniteType X.hom]

theorem auxiliary_quotient_baseChange_affine
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P K iotaO L N X) (hU : U.IsFine)
    (A : PEL.Has.IntegralPELObject P K iotaO N Y) (q : X ⟶ Y)
    [IsFinite q.left] [Etale q.left] [Surjective q.left]
    (e : PEL.Iso.PolarizedActionIso (A.pullback q).data U.forgetAuxiliary.data)
    (hN : 3 ≤ N) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) (φ : K →+* K')
    (hA : ∀ (T : Over (Spec (.of K'))) [IsReduced T.left]
      (B : PEL.Has.IntegralPELObject P K' (φ.comp iotaO) N T),
      ∃! f : T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y,
        Nonempty (PEL.Iso.PolarizedActionIso ((A.baseChange φ).pullback f).data B.data))
    (hred : IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left)
    (hsep : ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left.IsSeparated)
    (hAF : ∀ F : Set ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left,
      F.Finite → ∃ V : ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left.Opens,
        IsAffineOpen V ∧ F ⊆ V) :
    IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y).left ∧
    (∀ F : Set ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y).left,
      F.Finite → ∃ V : ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y).left.Opens,
        IsAffineOpen V ∧ F ⊆ V) := by
  let b := Spec.map (CommRingCat.ofHom φ)
  let q' := (Over.pullback b).map q
  have : IsFinite q'.left := MorphismProperty.of_isPullback (Specialization.base_change_square b q)
    (inferInstanceAs (IsFinite q.left))
  have : Etale q'.left := MorphismProperty.of_isPullback (Specialization.base_change_square b q)
    (inferInstanceAs (Etale q.left))
  have : Surjective q'.left := MorphismProperty.of_isPullback (Specialization.base_change_square b q)
    (inferInstanceAs (Surjective q.left))
  have : IsReduced ((Over.pullback b).obj X).left := hred
  have : ((Over.pullback b).obj X).left.IsSeparated := hsep
  have hu : (U.baseChange φ).IsFine := IntegralAdded.FineBaseChange.integralAddedPEL_fine_baseChange U hU φ
  let e' : PEL.Iso.PolarizedActionIso ((A.baseChange φ).pullback q').data
      (U.baseChange φ).forgetAuxiliary.data :=
    PEL.FamilyComparisonBaseChange.prescribedFamilyComparisonBaseChange A U.forgetAuxiliary q e φ
  have hk := IntegralAuxiliary.KernelPair.IntegralAuxiliaryAction.prescribed_map_kernelPair (U.baseChange φ) hu
    (CharacteristicZeroPrescribedRigidity.characteristicZero_baseChange_prescribedRigid U hN hPresentations φ) (A.baseChange φ) hA q' e'
  exact ⟨Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_finite_flat_surjective q'.left,
    AuxiliaryAffineNeighborhoodDescent.IntegralAuxiliaryAction.finite_set_affine_neighborhood_descends (U.baseChange φ) hu
      q'.left (hk.map (Over.forget (Spec (.of K')))) hAF⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuotientBaseChangeAffine
