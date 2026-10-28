import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.AdjunctionChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.EqualizerCongr
import OAI.AlgebraicGeometry.Picard.PoincareBundle.EqualizerTargetChange

/-! # Adjunction Invariant -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.AdjunctionInvariant

noncomputable section

/-!
# Canonical adjunction changes preserve Čech invariants and effectivity
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.AdjunctionChange

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {R : D ⥤ C} {P Q P' Q' : D ⥤ E} {U V U' V' : E ⥤ D}
  (b : P ⊣ U) (b' : P' ⊣ U') (c : Q ⊣ V) (c' : Q' ⊣ V')
  (α : P ≅ P') (β : Q ≅ Q') (ρ : U ≅ U') (τ : V ≅ V')
  (hP : conjugateEquiv b b' α.inv = ρ.hom) (hQ : conjugateEquiv c c' β.inv = τ.hom)
  (e : U ⋙ R ≅ V ⋙ R) [HasEqualizers C]
  {M : D} (σ : P.obj M ⟶ Q.obj M)

/-- The invariant object retains its identity up to canonical isomorphism when its adjunctions change. -/
def invariantIso : AdjointCechInvariant.invariants b' c' (AdjunctionChange.changedRightIso ρ τ e) (AdjunctionChange.changedGluing α β σ) ≅ AdjointCechInvariant.invariants b c e σ :=
  EqualizerCongr.iso (AdjunctionChange.leftMap_eq b b' α β ρ τ hP e σ)
      (AdjunctionChange.rightMap_eq (R := R) c c' β τ hQ (M := M)) ≪≫
    EqualizerTargetChange.equalizerIso (AdjointCechInvariant.leftMap b e σ) (AdjointCechInvariant.rightMap (R := R) c)
      (AdjunctionChange.targetIso (R := R) β τ (M := M)).hom

theorem invariantIso_hom_ι :
    (invariantIso b b' c c' α β ρ τ hP hQ e σ).hom ≫
      equalizer.ι (AdjointCechInvariant.leftMap b e σ) (AdjointCechInvariant.rightMap (R := R) c) =
    equalizer.ι (AdjointCechInvariant.leftMap b' (AdjunctionChange.changedRightIso ρ τ e) (AdjunctionChange.changedGluing α β σ)) (AdjointCechInvariant.rightMap (R := R) c') := by
  have ht := EqualizerTargetChange.hom_ι (AdjointCechInvariant.leftMap b e σ) (AdjointCechInvariant.rightMap (R := R) c)
    (AdjunctionChange.targetIso (R := R) β τ (M := M)).hom
  have hc := EqualizerCongr.hom_ι (AdjunctionChange.leftMap_eq b b' α β ρ τ hP e σ)
    (AdjunctionChange.rightMap_eq (R := R) c c' β τ hQ (M := M))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (EqualizerCongr.iso (AdjunctionChange.leftMap_eq b b' α β ρ τ hP e σ)
      (AdjunctionChange.rightMap_eq (R := R) c c' β τ hQ (M := M))).hom ≫ z) ht).trans hc)

variable {L : C ⥤ D} (a : L ⊣ R)

/-- The same change also retains the actual canonical comparison morphism. -/
theorem comparison_commutes :
    L.map (invariantIso b b' c c' α β ρ τ hP hQ e σ).hom ≫ AdjointCechInvariant.comparison a b c e σ =
      AdjointCechInvariant.comparison a b' c' (AdjunctionChange.changedRightIso ρ τ e) (AdjunctionChange.changedGluing α β σ) := by
  apply (a.homEquiv _ M).injective
  exact (AdjointCechInvariant.homEquiv_map_comparison a b c e σ (invariantIso b b' c c' α β ρ τ hP hQ e σ).hom).trans
    ((invariantIso_hom_ι b b' c c' α β ρ τ hP hQ e σ).trans
      (AdjointCechInvariant.comparison_homEquiv a b' c' (AdjunctionChange.changedRightIso ρ τ e) (AdjunctionChange.changedGluing α β σ)).symm)

include hP hQ in
/-- Invertibility of the canonical comparison is independent of the isomorphic adjunction choices. -/
theorem comparison_isIso_iff :
    IsIso (AdjointCechInvariant.comparison a b' c' (AdjunctionChange.changedRightIso ρ τ e) (AdjunctionChange.changedGluing α β σ)) ↔
      IsIso (AdjointCechInvariant.comparison a b c e σ) := by
  rw [← comparison_commutes b b' c c' α β ρ τ hP hQ e σ a]
  exact isIso_comp_left_iff _ _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.AdjunctionInvariant
