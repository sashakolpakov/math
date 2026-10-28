import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.AddedParameterClassification
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PureAddedLevelRigidity

/-! # Two Level Fine Away -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.TwoLevelFineAway

noncomputable section

/-! Construct a bounded integral two-level PEL parameter which is fine
on all reduced tests after inverting one coefficient. The pure classifier,
automorphism rigidity, and relative action representation are all used
with their actual universal families. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PureAddedLevelRigidity.IntegralPureModel

theorem exists_integral_two_level_pel_fine_away
    {E R K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [IsDomain R] [Field K] [CharZero K] [Countable K]
    (ι : R →+* K) (hι : Function.Injective ι)
    {s L N : ℕ} [NeZero N] (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R)
    (M : AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel (3 * s) P.polarizationType L (Spec (.of R)))
    [IsNoetherian M.space.left]
    (hM : M.IsFine) (hL : 3 ≤ L)
    (hft : LocallyOfFiniteType M.space.hom) (hqc : QuasiCompact M.space.hom)
    (hsep : IsSeparated M.space.hom)
    (hN : ∀ x : M.space.left, IsUnit (N : M.space.left.presheaf.stalk x))
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ x : M.space.left, IsUnit (D.conductor : M.space.left.presheaf.stalk x)) :
    ∃ r : R, r ≠ 0 ∧ ∃ V : Over (Spec (.of R)),
      IsReduced V.left ∧ IsNoetherian V.left ∧ LocallyOfFiniteType V.hom ∧
      QuasiCompact V.hom ∧ IsSeparated V.hom ∧
      ∃ U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N V,
        ∀ (T : Over (Spec (.of R))) [IsReduced T.left],
          (∀ x : T.left, r ∉ (T.hom x).asIdeal) →
          ∀ B : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N T,
            ∃! f : T ⟶ V, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback f) B) := by
  have : LocallyOfFiniteType M.space.hom := hft
  have : QuasiCompact M.space.hom := hqc
  have : IsSeparated M.space.hom := hsep
  let F := PureAddedLevel.IntegralPureModel.addedLevelSpace M hN (N := N)
  let A := PureAddedLevel.IntegralPureModel.addedLevelUniversal M hN (N := N)
  let q := (PureAddedLevel.IntegralPureModel.prescribedFrame M hN (N := N)).hom
  have : IsFinite q := inferInstanceAs (IsFinite (PureAddedLevel.IntegralPureModel.addedLevelForget M hN (N := N)).left)
  have : IsLocallyNoetherian F.left := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace F.left := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian F.left := ⟨⟩
  have : LocallyOfFiniteType F.hom := by change LocallyOfFiniteType (q ≫ M.space.hom); infer_instance
  have : QuasiCompact F.hom := by change QuasiCompact (q ≫ M.space.hom); infer_instance
  have : IsSeparated F.hom := by change IsSeparated (q ≫ M.space.hom); infer_instance
  obtain ⟨r₁, hr₁, hFine⟩ := PureAddedLevelRigidity.IntegralPureModel.addedLevel_reduced_isFine_away ι hι M hM hL hN hPresentations
  obtain ⟨r₂, hr₂, hRigid⟩ := GlobalReducedPolarizedRigidity.polarized_reduced_rigidity_away ι hι F.hom A.auxiliary hL hPresentations
  obtain ⟨Z, hr, hn, hZft, hZqc, hZsep, u, hclass⟩ :=
    GlobalRelativeAction.exists_global_relative_pel_action_representation P iotaO F A.auxiliary D hPresentations (fun x => by
      simpa only [map_natCast] using (hc (q x)).map (q.stalkMap x).hom)
  let V := (Over.map F.hom).obj Z
  have : IsReduced V.left := hr
  have : IsNoetherian V.left := hn
  have : LocallyOfFiniteType Z.hom := hZft
  have : QuasiCompact Z.hom := hZqc
  have : IsSeparated Z.hom := hZsep
  have : LocallyOfFiniteType V.hom := by change LocallyOfFiniteType (Z.hom ≫ F.hom); infer_instance
  have : QuasiCompact V.hom := by change QuasiCompact (Z.hom ≫ F.hom); infer_instance
  have : IsSeparated V.hom := by change IsSeparated (Z.hom ≫ F.hom); infer_instance
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, V, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, Relative.AddedFamily.relativeAddedPELUniversal P iotaO F A Z u, ?_⟩
  intro T _ hunit B
  have h₁ (x : T.left) : r₁ ∉ (T.hom x).asIdeal :=
    fun h => hunit x ((T.hom x).asIdeal.mem_of_dvd (dvd_mul_right r₁ r₂) h)
  have h₂ (x : T.left) : r₂ ∉ (T.hom x).asIdeal :=
    fun h => hunit x ((T.hom x).asIdeal.mem_of_dvd (dvd_mul_left r₂ r₁) h)
  apply Relative.AddedParameterClassification.relativeAddedPELParameter_classifies P iotaO F A u hclass T (hFine T h₁) ?_ B
  intro f e
  have : IsReduced (Over.mk f.left).left := inferInstanceAs (IsReduced T.left)
  apply hRigid (Over.mk f.left) e
  intro x
  have hx : F.hom (f.left x) = T.hom x := congrArg (fun a : T.left ⟶ Spec (.of R) => a x) f.w
  exact hx.symm ▸ h₂ x

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.TwoLevelFineAway
