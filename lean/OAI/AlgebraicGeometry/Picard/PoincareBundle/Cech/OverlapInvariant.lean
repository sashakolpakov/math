import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.OverlapExtension
import OAI.AlgebraicGeometry.Picard.PoincareBundle.EqualizerTargetChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.EqualizerCongr

/-! # Overlap Invariant -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.OverlapInvariant

noncomputable section

/-!
# Fully faithful overlap extension preserves the actual invariant and its comparison
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.OverlapExtension

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {R : D ⥤ C} {P Q : D ⥤ E} {U V : E ⥤ D} {J : E ⥤ F} {K : F ⥤ E}
  (b : P ⊣ U) (c : Q ⊣ V) (e : U ⋙ R ≅ V ⋙ R) (d : J ⊣ K)
  [J.Full] [J.Faithful] [HasEqualizers C]
  {M : D} (σ : P.obj M ⟶ Q.obj M)

/-- The extended overlap yields the same actual invariant equalizer. -/
def invariantIso :
    AdjointCechInvariant.invariants (b.comp d) (c.comp d) (OverlapExtension.extendedRightIso e) (J.map σ) ≅ AdjointCechInvariant.invariants b c e σ :=
  EqualizerCongr.iso (OverlapExtension.leftMap_eq b e d σ) (OverlapExtension.rightMap_eq (R := R) c d (M := M)) ≪≫
    EqualizerTargetChange.equalizerIso (AdjointCechInvariant.leftMap b e σ) (AdjointCechInvariant.rightMap (R := R) c)
      (OverlapExtension.targetMap (R := R) (Q := Q) (V := V) d (M := M))

/-- This isomorphism retains the original invariant inclusion into the direct image. -/
theorem invariantIso_hom_ι :
    (invariantIso b c e d σ).hom ≫ equalizer.ι (AdjointCechInvariant.leftMap b e σ) (AdjointCechInvariant.rightMap (R := R) c) =
      equalizer.ι (AdjointCechInvariant.leftMap (Q := Q ⋙ J) (b.comp d) (OverlapExtension.extendedRightIso e) (J.map σ))
        (AdjointCechInvariant.rightMap (R := R) (c.comp d)) := by
  have ht := EqualizerTargetChange.hom_ι (AdjointCechInvariant.leftMap b e σ) (AdjointCechInvariant.rightMap (R := R) c)
    (OverlapExtension.targetMap (R := R) (Q := Q) (V := V) d (M := M))
  have hc := EqualizerCongr.hom_ι (OverlapExtension.leftMap_eq b e d σ) (OverlapExtension.rightMap_eq (R := R) c d (M := M))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z =>
      (EqualizerCongr.iso (OverlapExtension.leftMap_eq b e d σ) (OverlapExtension.rightMap_eq (R := R) c d (M := M))).hom ≫ z)
      ht).trans hc)

variable {L : C ⥤ D} (a : L ⊣ R)

/-- The canonical pullback comparison is retained, not just the invariant object. -/
theorem comparison_commutes :
    L.map (invariantIso b c e d σ).hom ≫ AdjointCechInvariant.comparison a b c e σ =
      AdjointCechInvariant.comparison a (b.comp d) (c.comp d) (OverlapExtension.extendedRightIso e) (J.map σ) := by
  apply (a.homEquiv _ M).injective
  exact (AdjointCechInvariant.homEquiv_map_comparison a b c e σ (invariantIso b c e d σ).hom).trans
    ((invariantIso_hom_ι b c e d σ).trans
      (AdjointCechInvariant.comparison_homEquiv a (b.comp d) (c.comp d) (OverlapExtension.extendedRightIso e) (J.map σ)).symm)

/-- Effectivity is unchanged by fully faithful extension of the overlap presentation. -/
theorem comparison_isIso_iff :
    IsIso (AdjointCechInvariant.comparison a (b.comp d) (c.comp d) (OverlapExtension.extendedRightIso e) (J.map σ)) ↔
      IsIso (AdjointCechInvariant.comparison a b c e σ) := by
  rw [← comparison_commutes b c e d σ a]
  exact isIso_comp_left_iff _ _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.OverlapInvariant
