import OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointSquareHom
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.AdjunctionChange

/-! # Restriction Arrows -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.RestrictionArrows

noncomputable section

/-!
# Base change of the two actual Čech invariant arrows
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor

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

open OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentRestriction OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant

/-- Coherence of the three canonical direct-image base-change maps. -/
def RightCoherent : Prop := ∀ W : E,
  G.map (e.hom.app W) ≫ (DescentRestriction.rightMate a a' α).app (V.obj W) ≫ R'.map ((DescentRestriction.rightMate c c' γ).app W) =
    (DescentRestriction.rightMate a a' α).app (U.obj W) ≫ R'.map ((DescentRestriction.rightMate b b' β).app W) ≫ e'.hom.app (J.obj W)

variable {M : D} (σ : P.obj M ⟶ Q.obj M)

/-- The original gluing transported by the two left-adjoint base-change squares. -/
def restrictedGluing : P'.obj (H.obj M) ⟶ Q'.obj (H.obj M) :=
  (β.hom.app M ≫ J.map σ) ≫ γ.inv.app M

/-- The target map of the invariant equalizer diagram under base change. -/
def targetMap : G.obj ((V ⋙ R).obj (Q.obj M)) ⟶ (V' ⋙ R').obj (Q'.obj (H.obj M)) :=
  (DescentRestriction.rightMate a a' α).app (V.obj (Q.obj M)) ≫ R'.map ((DescentRestriction.rightMate c c' γ).app (Q.obj M)) ≫
    R'.map (V'.map (γ.inv.app M))

/-- The restricted first arrow can be computed through the transported adjoint gluing. -/
theorem restricted_leftMap :
    AdjointCechInvariant.leftMap b' e' (restrictedGluing β γ σ) =
      R'.map ((H.map (b.homEquiv M (Q.obj M) σ) ≫ (DescentRestriction.rightMate b b' β).app (Q.obj M)) ≫
        U'.map (γ.inv.app M)) ≫ e'.hom.app (Q'.obj (H.obj M)) := by
  rw [AdjunctionChange.leftMap_homEquiv]
  exact congrArg (fun t => R'.map t ≫ e'.hom.app (Q'.obj (H.obj M)))
    (AdjointSquareHom.homEquiv_restrict_comp b b' β σ (γ.inv.app M))

include e in
/-- Coherent base change carries the first Čech invariant arrow to the restricted first arrow. -/
theorem leftMap_square (hc : RightCoherent a a' b b' c c' α β γ e e') :
    G.map (AdjointCechInvariant.leftMap b e σ) ≫ targetMap a a' c c' α γ (M := M) =
      (DescentRestriction.rightMate a a' α).app M ≫ AdjointCechInvariant.leftMap b' e' (restrictedGluing β γ σ) := by
  rw [AdjunctionChange.leftMap_homEquiv, restricted_leftMap b b' β γ e' σ]
  simp only [targetMap, Functor.map_comp, Category.assoc]
  slice_lhs 2 4 => exact hc (Q.obj M)
  simp only [Category.assoc]
  slice_lhs 4 5 => exact (e'.hom.naturality (γ.inv.app M)).symm
  slice_lhs 1 2 => exact (DescentRestriction.rightMate a a' α).naturality (b.homEquiv M (Q.obj M) σ)
  simp only [Category.assoc]
  rfl

/-- The unit identity for the second projection gives the second Čech invariant square. -/
theorem rightMap_square :
    G.map (AdjointCechInvariant.rightMap (R := R) c (M := M)) ≫ targetMap a a' c c' α γ (M := M) =
      (DescentRestriction.rightMate a a' α).app M ≫ AdjointCechInvariant.rightMap (R := R') c' (M := H.obj M) := by
  change G.map (R.map (c.unit.app M)) ≫
    ((DescentRestriction.rightMate a a' α).app (V.obj (Q.obj M)) ≫ R'.map ((DescentRestriction.rightMate c c' γ).app (Q.obj M)) ≫
      R'.map (V'.map (γ.inv.app M))) =
    (DescentRestriction.rightMate a a' α).app M ≫ R'.map (c'.unit.app (H.obj M))
  rw [DescentRestriction.unit_via_rightMate c c' γ M]
  simp only [Functor.map_comp]
  slice_lhs 1 2 => exact (DescentRestriction.rightMate a a' α).naturality (c.unit.app M)
  simp only [Category.assoc]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.RestrictionArrows
