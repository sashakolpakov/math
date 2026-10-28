import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PureAddedLevel
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalReducedPolarizedRigidity

/-! # Pure Added Level Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PureAddedLevelRigidity

noncomputable section

/-! The actual integral two-level pure parameter becomes fine on all
reduced tests after a single coefficient is inverted. The coefficient
and uniqueness follow from the constructed bounded automorphism loci. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace IntegralPureModel

theorem addedLevel_reduced_isFine_away
    {R K : Type} [CommRing R] [IsDomain R] [Field K] [CharZero K] [Countable K]
    (ι : R →+* K) (hι : Function.Injective ι)
    {g L N : ℕ} {δ : Fin g → ℕ} [NeZero N]
    (M : AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel g δ L (Spec (.of R)))
    [IsNoetherian M.space.left] [LocallyOfFiniteType M.space.hom]
    (hM : M.IsFine) (hL : 3 ≤ L)
    (hN : ∀ x : M.space.left, IsUnit (N : M.space.left.presheaf.stalk x))
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) :
    ∃ r : R, r ≠ 0 ∧ ∀ (T : Over (Spec (.of R))) [IsReduced T.left],
      (∀ x : T.left, r ∉ (T.hom x).asIdeal) →
      ∀ A : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel g δ L N T.left,
        ∃! j : T ⟶ PureAddedLevel.IntegralPureModel.addedLevelSpace M hN,
          Nonempty (AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso ((PureAddedLevel.IntegralPureModel.addedLevelUniversal M hN).pullback j.left) A) := by
  obtain ⟨r, hr, hrigid⟩ := GlobalReducedPolarizedRigidity.polarized_reduced_rigidity_away ι hι M.space.hom M.universal hL hPresentations
  refine ⟨r, hr, ?_⟩
  intro T _ hunit A
  obtain ⟨j, ⟨a⟩⟩ := PureAddedLevel.IntegralPureModel.addedLevel_classifying_exists M hN hM T A
  refine ⟨j, ⟨a⟩, ?_⟩
  rintro k ⟨b⟩
  apply PureAddedLevel.IntegralPureModel.addedLevel_classifying_unique_of_rigidity M hN hM T A ?_ k j b a
  intro f e
  have : IsReduced (Over.mk f.left).left := inferInstanceAs (IsReduced T.left)
  apply hrigid (Over.mk f.left) e
  intro x
  have hx := congrArg (fun q : T.left ⟶ Spec (.of R) => q x) f.w
  exact hx.symm ▸ hunit x

end IntegralPureModel

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PureAddedLevelRigidity
