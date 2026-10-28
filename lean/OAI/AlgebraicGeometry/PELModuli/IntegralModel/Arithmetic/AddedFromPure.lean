import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.TwoLevelFineAway
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.LocalizationMaps

/-! # Added From Pure -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AddedFromPure

noncomputable section

/-! An actual pure fine model supplies the arithmetic added-level PEL
parameter after an integer denominator is enlarged. The universal family
is the existing integral classifier followed by its actual base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem integerUnit_at_stalk {R : Type} [CommRing R]
    {S : Scheme.{0}} (p : S ⟶ Spec (.of R)) (n : ℕ)
    (hn : IsUnit (n : R)) (x : S) : IsUnit (n : S.presheaf.stalk x) := by
  let constants : R →+* Γ(S, ⊤) :=
    p.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let toStalk : R →+* S.presheaf.stalk x :=
    (S.presheaf.germ ⊤ x (by trivial)).hom.comp constants
  simpa only [map_natCast] using hn.map toStalk

theorem exists_arithmetic_added_pel_fine_model_from_pureModel
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) {s L N : ℕ} [NeZero N]
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (iota : E →+* K)
    (M : AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel (3 * s) P.polarizationType L B.base)
    (hM : M.IsFine) (Q : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space)
    (hL : 3 ≤ L) (hNunit : IsUnit (N : B.R))
    (G : CM.GeneratorReconstruction.CMIntegralGeneratorData E) (hc : IsUnit (G.conductor : B.R))
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) :
    ∃ (D : ℕ) (hD : D ≠ 0), N ∣ D ∧ B.denominator ∣ D ∧
      let B' := B.withDenominator D hD
      ∃ φ : B.R →+* B'.R, B'.toField.comp φ = B.toField ∧
        ∃ V : Over B'.base, IsReduced V.left ∧ IsNoetherian V.left ∧
          LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom ∧
          ∃ U : IntegralAdded.PELId.IntegralAddedPELLevel P B'.R (B'.integralEmbedding iota) L N V,
            ∀ (T : Over B'.base) [IsReduced T.left]
              (A : IntegralAdded.PELId.IntegralAddedPELLevel P B'.R (B'.integralEmbedding iota) L N T),
              ∃! f : T ⟶ V, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback f) A) := by
  have : IsDomain B.R := Function.Injective.isDomain B.toField B.toField_injective
  have : Countable B.extension.carrier :=
    AbelianScheme.TateComparison.CountableResidueFields.countable_finiteType ℚ B.extension.carrier
  have : LocallyOfFiniteType M.space.hom := Q.locallyFiniteType
  have : QuasiCompact M.space.hom := Q.quasiCompact
  have : IsLocallyNoetherian M.space.left :=
    LocallyOfFiniteType.isLocallyNoetherian M.space.hom
  have : CompactSpace M.space.left := QuasiCompact.compactSpace_of_compactSpace M.space.hom
  have : IsNoetherian M.space.left := ⟨⟩
  obtain ⟨r, hr, X, hred, hn, hft, hqc, hsep, U, hclass⟩ :=
    Integral.TwoLevelFineAway.exists_integral_two_level_pel_fine_away B.toField B.toField_injective
      P (B.integralEmbedding iota) M hM hL Q.locallyFiniteType Q.quasiCompact
      Q.separated (integerUnit_at_stalk M.space.hom N hNunit) G hPresentations
      (integerUnit_at_stalk M.space.hom G.conductor hc)
  obtain ⟨D, hD, hND, hBD, φ, hφ, hunit⟩ :=
    B.coefficient_isUnit_after_localization r hr N (NeZero.ne N)
  let B' := B.withDenominator D hD
  let b := Spec.map (CommRingCat.ofHom φ)
  let V := (Over.pullback b).obj X
  have : IsOpenImmersion b := B.coefficient_map_isOpenImmersion D hD φ hφ
  have : IsReduced X.left := hred
  have : IsNoetherian X.left := hn
  have : LocallyOfFiniteType X.hom := hft
  have : QuasiCompact X.hom := hqc
  have : IsSeparated X.hom := hsep
  have : IsReduced V.left := isReduced_of_isOpenImmersion (pullback.fst X.hom b)
  have : LocallyOfFiniteType V.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom b))
  have : QuasiCompact V.hom := inferInstanceAs (QuasiCompact (pullback.snd X.hom b))
  have : IsSeparated V.hom := inferInstanceAs (IsSeparated (pullback.snd X.hom b))
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  have : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace V.hom
  have : IsNoetherian V.left := ⟨⟩
  refine ⟨D, hD, hND, hBD, φ, hφ, V, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  have hI := B.coefficient_map_integralEmbedding D hD φ hφ iota
  have hf : ∃ W : IntegralAdded.PELId.IntegralAddedPELLevel P B'.R (φ.comp (B.integralEmbedding iota)) L N V,
      ∀ (T : Over B'.base) [IsReduced T.left]
        (A : IntegralAdded.PELId.IntegralAddedPELLevel P B'.R (φ.comp (B.integralEmbedding iota)) L N T),
        ∃! f : T ⟶ V, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso (W.pullback f) A) :=
    ⟨U.baseChange φ, fun T _ A =>
      IntegralAdded.FineBaseChange.integralAddedPEL_fine_baseChange_of_unit U r hclass φ hunit T A⟩
  exact hI ▸ hf

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AddedFromPure
