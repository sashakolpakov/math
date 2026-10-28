import Mathlib.AlgebraicGeometry.Restrict

/-! # Cartesian Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.CartesianRestriction

noncomputable section

/-! A cartesian family whose coefficient map lands in an open subset
has actual compatible lifts to the restricted family and base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem exists_cartesian_open_lifts
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (a : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S)
    (hp : IsPullback a ρ f g) (U : S.Opens) (hU : Set.range g ⊆ (U : Set S)) :
    ∃ (b : Y ⟶ (f ⁻¹ᵁ U).toScheme) (k : T ⟶ U.toScheme),
      b ≫ (f ⁻¹ᵁ U).ι = a ∧ k ≫ U.ι = g ∧ IsPullback b ρ (f ∣_ U) k := by
  have hr : Set.range g ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact hU
  let k := IsOpenImmersion.lift U.ι g hr
  have hk : k ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  have har : Set.range a ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    change f (a y) ∈ U
    have he : f (a y) = g (ρ y) := congrArg (fun z : Y ⟶ S => z y) hp.w
    exact he ▸ hU ⟨ρ y, rfl⟩
  let b := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι a har
  have hb : b ≫ (f ⁻¹ᵁ U).ι = a := IsOpenImmersion.lift_fac _ _ _
  have hw : b ≫ (f ∣_ U) = ρ ≫ k := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hb,
      Category.assoc, hk]
    exact hp.w
  have hout : IsPullback (b ≫ (f ⁻¹ᵁ U).ι) ρ f (k ≫ U.ι) := by
    rw [hb, hk]
    exact hp
  exact ⟨b, k, hb, hk, hout.of_right hw (isPullback_morphismRestrict f U).flip⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.CartesianRestriction
