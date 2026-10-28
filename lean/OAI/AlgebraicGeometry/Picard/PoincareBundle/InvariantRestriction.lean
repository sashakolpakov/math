import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentRestriction
import Mathlib.CategoryTheory.Monad.Comonadicity
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Invariant Restriction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.InvariantRestriction

noncomputable section

/-!
# Base change of invariant objects for PoincareBundle

If the right-adjoint base-change map is invertible and restriction
preserves the defining equalizer, invariant objects commute with
restriction. The comparison is built from an isomorphism of the two
equalizer diagrams.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Comonad

universe u v

variable {C D E F : Type u} [Category.{v} C] [Category.{v} D]
  [Category.{v} E] [Category.{v} F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G : C ⥤ E} {H : D ⥤ F}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : G ⋙ L₂ ≅ L₁ ⋙ H)
  [IsIso (DescentRestriction.rightMate adj₁ adj₂ α)]

/-- The source isomorphism between the invariant diagrams. -/
def pairSourceIso (A : adj₁.toComonad.Coalgebra) :
    G.obj (R₁.obj A.A) ≅ R₂.obj (H.obj A.A) :=
  asIso ((DescentRestriction.rightMate adj₁ adj₂ α).app A.A)

/-- The target isomorphism between the invariant diagrams. -/
def pairTargetIso (A : adj₁.toComonad.Coalgebra) :
    G.obj (R₁.obj (L₁.obj (R₁.obj A.A))) ≅
      R₂.obj (L₂.obj (R₂.obj (H.obj A.A))) :=
  asIso ((DescentRestriction.rightMate adj₁ adj₂ α).app (L₁.obj (R₁.obj A.A))) ≪≫
    R₂.mapIso ((α.app (R₁.obj A.A)).symm ≪≫
      L₂.mapIso (pairSourceIso adj₁ adj₂ α A))

/-- Compatibility with the coaction map in the invariant diagram. -/
theorem pair_coaction (A : adj₁.toComonad.Coalgebra) :
    G.map (R₁.map A.a) ≫ (pairTargetIso adj₁ adj₂ α A).hom =
      (pairSourceIso adj₁ adj₂ α A).hom ≫
        R₂.map (DescentRestriction.restrictedCoaction adj₁ adj₂ α A) := by
  change G.map (R₁.map A.a) ≫
      (DescentRestriction.rightMate adj₁ adj₂ α).app (L₁.obj (R₁.obj A.A)) ≫
        R₂.map (α.inv.app (R₁.obj A.A) ≫
          L₂.map ((DescentRestriction.rightMate adj₁ adj₂ α).app A.A)) =
    (DescentRestriction.rightMate adj₁ adj₂ α).app A.A ≫
      R₂.map (H.map A.a ≫ α.inv.app (R₁.obj A.A) ≫
        L₂.map ((DescentRestriction.rightMate adj₁ adj₂ α).app A.A))
  erw [← Category.assoc,
    (DescentRestriction.rightMate adj₁ adj₂ α).naturality A.a,
    Category.assoc, ← R₂.map_comp]
  rfl

/-- Compatibility with the adjunction unit in the invariant diagram. -/
theorem pair_unit (A : adj₁.toComonad.Coalgebra) :
    G.map (adj₁.unit.app (R₁.obj A.A)) ≫ (pairTargetIso adj₁ adj₂ α A).hom =
      (pairSourceIso adj₁ adj₂ α A).hom ≫ adj₂.unit.app (R₂.obj (H.obj A.A)) := by
  change G.map (adj₁.unit.app (R₁.obj A.A)) ≫
      (DescentRestriction.rightMate adj₁ adj₂ α).app (L₁.obj (R₁.obj A.A)) ≫
        R₂.map (α.inv.app (R₁.obj A.A) ≫
          L₂.map ((DescentRestriction.rightMate adj₁ adj₂ α).app A.A)) =
    (DescentRestriction.rightMate adj₁ adj₂ α).app A.A ≫
      adj₂.unit.app (R₂.obj (H.obj A.A))
  erw [← adj₂.unit_naturality
    ((DescentRestriction.rightMate adj₁ adj₂ α).app A.A),
    DescentRestriction.unit_via_rightMate adj₁ adj₂ α (R₁.obj A.A),
    R₂.map_comp (α.inv.app (R₁.obj A.A))
      (L₂.map ((DescentRestriction.rightMate adj₁ adj₂ α).app A.A)),
    ]
  exact ((Category.assoc (G.map (adj₁.unit.app (R₁.obj A.A)))
      ((DescentRestriction.rightMate adj₁ adj₂ α).app (L₁.obj (R₁.obj A.A)) ≫
        R₂.map (α.inv.app (R₁.obj A.A)))
      (R₂.map (L₂.map ((DescentRestriction.rightMate adj₁ adj₂ α).app A.A)))).trans
    (congrArg (fun k => G.map (adj₁.unit.app (R₁.obj A.A)) ≫ k)
      (Category.assoc
        ((DescentRestriction.rightMate adj₁ adj₂ α).app (L₁.obj (R₁.obj A.A)))
        (R₂.map (α.inv.app (R₁.obj A.A)))
        (R₂.map (L₂.map ((DescentRestriction.rightMate adj₁ adj₂ α).app A.A)))))).symm

variable [HasEqualizers C] [HasEqualizers E] [PreservesFiniteLimits G]

/-- The explicit invariant object commutes with restriction when the
right mate is invertible and restriction preserves equalizers. -/
def invariantRestrictionIso (A : adj₁.toComonad.Coalgebra) :
    G.obj (ComonadicityInternal.comparisonRightAdjointObj adj₁ A) ≅
      ComonadicityInternal.comparisonRightAdjointObj adj₂
        ((DescentRestriction.coalgebraRestriction adj₁ adj₂ α).obj A) :=
  PreservesEqualizer.iso G (R₁.map A.a) (adj₁.unit.app (R₁.obj A.A)) ≪≫
    HasLimit.isoOfNatIso (parallelPair.ext (pairSourceIso adj₁ adj₂ α A)
      (pairTargetIso adj₁ adj₂ α A)
      (pair_coaction adj₁ adj₂ α A) (pair_unit adj₁ adj₂ α A))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.InvariantRestriction
