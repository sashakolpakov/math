import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.RestrictionArrows
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Invariant Restriction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantRestriction

noncomputable section

/-!
# The actual Čech invariant equalizer commutes with coherent base change
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits

universe u v

variable {C D E C' D' E' : Type u}
  [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [Category.{v} C'] [Category.{v} D'] [Category.{v} E']
  {L : C ⥤ D} {R : D ⥤ C} {P Q : D ⥤ E} {U V : E ⥤ D}
  {L' : C' ⥤ D'} {R' : D' ⥤ C'} {P' Q' : D' ⥤ E'} {U' V' : E' ⥤ D'}
  {G : C ⥤ C'} {H : D ⥤ D'} {J : E ⥤ E'}
  (a : L ⊣ R) (a' : L' ⊣ R') (b : P ⊣ U) (b' : P' ⊣ U')
  (c : Q ⊣ V) (c' : Q' ⊣ V')
  (α : G ⋙ L' ≅ L ⋙ H) (β : H ⋙ P' ≅ P ⋙ J) (γ : H ⋙ Q' ≅ Q ⋙ J)
  (e : U ⋙ R ≅ V ⋙ R) (e' : U' ⋙ R' ≅ V' ⋙ R')

open OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentRestriction OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.RestrictionArrows

variable [IsIso (DescentRestriction.rightMate a a' α)] [IsIso (DescentRestriction.rightMate c c' γ)]

/-- Invertible right mates make the comparison of invariant diagram targets invertible. -/
instance targetMap_isIso (M : D) : IsIso (RestrictionArrows.targetMap a a' c c' α γ (M := M)) := by
  unfold RestrictionArrows.targetMap
  infer_instance

variable [HasEqualizers C] [HasEqualizers C'] [PreservesFiniteLimits G]
  {M : D} (σ : P.obj M ⟶ Q.obj M) (hc : RestrictionArrows.RightCoherent a a' b b' c c' α β γ e e')

/-- The invariant is transported by the actual isomorphism of its two-arrow diagram. -/
def invariantIso :
    G.obj (AdjointCechInvariant.invariants b c e σ) ≅ AdjointCechInvariant.invariants b' c' e' (RestrictionArrows.restrictedGluing β γ σ) :=
  PreservesEqualizer.iso G (AdjointCechInvariant.leftMap b e σ) (AdjointCechInvariant.rightMap (R := R) c) ≪≫
    HasLimit.isoOfNatIso (parallelPair.ext (asIso ((DescentRestriction.rightMate a a' α).app M))
      (asIso (RestrictionArrows.targetMap a a' c c' α γ (M := M)))
      (RestrictionArrows.leftMap_square a a' b b' c c' α β γ e e' σ hc)
      (RestrictionArrows.rightMap_square a a' c c' α γ (M := M)))

/-- The restriction identification retains the actual equalizer inclusion. -/
theorem invariantIso_hom_ι :
    (invariantIso a a' b b' c c' α β γ e e' σ hc).hom ≫
      equalizer.ι (AdjointCechInvariant.leftMap b' e' (RestrictionArrows.restrictedGluing β γ σ)) (AdjointCechInvariant.rightMap (R := R') c') =
    G.map (equalizer.ι (AdjointCechInvariant.leftMap b e σ) (AdjointCechInvariant.rightMap (R := R) c)) ≫ (DescentRestriction.rightMate a a' α).app M := by
  dsimp only [invariantIso]
  erw [Iso.trans_hom, Category.assoc]
  dsimp only [equalizer.ι]
  erw [HasLimit.isoOfNatIso_hom_π]
  change (PreservesEqualizer.iso G (AdjointCechInvariant.leftMap b e σ) (AdjointCechInvariant.rightMap (R := R) c)).hom ≫
    equalizer.ι _ _ ≫ (DescentRestriction.rightMate a a' α).app M = _
  erw [← Category.assoc, PreservesEqualizer.iso_hom, equalizerComparison_comp_π]

/-- Restriction also retains the actual canonical pullback comparison. -/
theorem comparison_fac :
    L'.map (invariantIso a a' b b' c c' α β γ e e' σ hc).hom ≫
      AdjointCechInvariant.comparison a' b' c' e' (RestrictionArrows.restrictedGluing β γ σ) =
    α.hom.app (AdjointCechInvariant.invariants b c e σ) ≫ H.map (AdjointCechInvariant.comparison a b c e σ) := by
  apply (a'.homEquiv _ _).injective
  rw [AdjointCechInvariant.homEquiv_map_comparison, AdjointSquareHom.homEquiv_restrict a a' α,
    AdjointCechInvariant.comparison_homEquiv]
  exact invariantIso_hom_ι a a' b b' c c' α β γ e e' σ hc

include hc in
/-- The original comparison is locally invertible exactly when the restricted one is invertible. -/
theorem comparison_map_isIso_iff :
    IsIso (H.map (AdjointCechInvariant.comparison a b c e σ)) ↔
      IsIso (AdjointCechInvariant.comparison a' b' c' e' (RestrictionArrows.restrictedGluing β γ σ)) := by
  calc
    IsIso (H.map (AdjointCechInvariant.comparison a b c e σ)) ↔
        IsIso (α.hom.app (AdjointCechInvariant.invariants b c e σ) ≫ H.map (AdjointCechInvariant.comparison a b c e σ)) :=
      (isIso_comp_left_iff _ _).symm
    _ ↔ IsIso (L'.map (invariantIso a a' b b' c c' α β γ e e' σ hc).hom ≫
        AdjointCechInvariant.comparison a' b' c' e' (RestrictionArrows.restrictedGluing β γ σ)) := by
      rw [comparison_fac a a' b b' c c' α β γ e e' σ hc]
    _ ↔ IsIso (AdjointCechInvariant.comparison a' b' c' e' (RestrictionArrows.restrictedGluing β γ σ)) := isIso_comp_left_iff _ _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantRestriction
