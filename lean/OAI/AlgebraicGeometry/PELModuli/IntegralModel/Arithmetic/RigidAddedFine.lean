import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.RigidityBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.LocalizationMaps
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalReducedPolarizedRigidity

/-! # Rigid Added Fine -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.RigidAddedFine

noncomputable section

/-! Localize the precise arithmetic base once more so the actual fine
two-level family has prescribed-level rigidity on every reduced test.
Both fineness and the prescribed integral coefficient embedding persist. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem exists_arithmetic_rigid_added_pel_fine_model
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s L N : ℕ} [NeZero N] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} (iota : E →+* K)
    {X : Over B.base} [IsReduced X.left] [IsNoetherian X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) L N X) (hU : U.IsFine)
    (hN : 3 ≤ N) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) :
    ∃ (D : ℕ) (hD : D ≠ 0), N ∣ D ∧ B.denominator ∣ D ∧
      let B' := B.withDenominator D hD
      ∃ φ : B.R →+* B'.R, B'.toField.comp φ = B.toField ∧
        ∃ V : Over B'.base, IsReduced V.left ∧ IsNoetherian V.left ∧
          LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom ∧
          ∃ A : IntegralAdded.PELId.IntegralAddedPELLevel P B'.R (B'.integralEmbedding iota) L N V,
            A.IsFine ∧ A.PrescribedRigid := by
  have : IsDomain B.R := Function.Injective.isDomain B.toField B.toField_injective
  have : Countable B.extension.carrier := AbelianScheme.TateComparison.CountableResidueFields.countable_finiteType ℚ B.extension.carrier
  obtain ⟨r, hr, hrigid⟩ := GlobalReducedPolarizedRigidity.polarized_reduced_rigidity_away B.toField B.toField_injective
    X.hom U.forgetAuxiliary.data.polarized hN hPresentations
  obtain ⟨D, hD, hND, hBD, φ, hφ, hunit⟩ :=
    B.coefficient_isUnit_after_localization r hr N (NeZero.ne N)
  let B' := B.withDenominator D hD
  let b := Spec.map (CommRingCat.ofHom φ)
  let V := (Over.pullback b).obj X
  have : IsOpenImmersion b := B.coefficient_map_isOpenImmersion D hD φ hφ
  have : IsReduced V.left := isReduced_of_isOpenImmersion (pullback.fst X.hom b)
  have : LocallyOfFiniteType V.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom b))
  have : QuasiCompact V.hom := inferInstanceAs (QuasiCompact (pullback.snd X.hom b))
  have : IsSeparated V.hom := inferInstanceAs (IsSeparated (pullback.snd X.hom b))
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  have : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace V.hom
  have : IsNoetherian V.left := ⟨⟩
  have hI := B.coefficient_map_integralEmbedding D hD φ hφ iota
  let A := (U.baseChange φ).changeEmbedding hI
  have hA : A.IsFine := IntegralAdded.PELId.integralAddedPEL_fine_changeEmbedding (U.baseChange φ) hI
    (IntegralAdded.FineBaseChange.integralAddedPEL_fine_baseChange U hU φ)
  have hAr : A.PrescribedRigid := IntegralPrescribed.RigidityBaseChange.integralAddedPEL_prescribedRigid_baseChange_of_away
    U r hrigid φ hunit
  exact ⟨D, hD, hND, hBD, φ, hφ, V, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, A, hA, hAr⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.RigidAddedFine
