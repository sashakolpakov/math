import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentRestriction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.BaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.BeckDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.Adjunction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InvariantRestriction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleLocality

/-! # Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.Descent

noncomputable section

/-!
# Restriction of geometric descent data for PoincareBundle

Global descent coactions restrict to every open of the base. The
restricted coaction satisfies both compatibility equations, and a line
bundle remains a line bundle after this restriction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- The canonical right-adjoint base-change map for open restriction. -/
def canonicalPushforwardBaseChange :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor U.ι ⟶
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward (f ∣_ U) :=
  DescentRestriction.rightMate
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
    (Adjunction.adjointPullbackSquare f U)

/-- Restriction of the full geometric descent datum to an open of the base. -/
def restrictDatum : BeckDescent.SheafDatum f ⥤
    BeckDescent.SheafDatum (f ∣_ U) :=
  DescentRestriction.coalgebraRestriction
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
    (Adjunction.adjointPullbackSquare f U)

/-- The underlying sheaf of restricted descent data is the geometric restriction. -/
theorem restrictDatum_obj_A (D : BeckDescent.SheafDatum f) :
    ((restrictDatum f U).obj D).A =
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj D.A := rfl

/-- Restricting a descent datum on a line bundle preserves local rank one. -/
theorem restrictDatum_isLine (D : BeckDescent.SheafDatum f)
    (hD : Line.Bundles.IsLine D.A) :
    Line.Bundles.IsLine ((restrictDatum f U).obj D).A :=
  (hD.pullback (f ⁻¹ᵁ U).ι).of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app D.A).symm

/-- The globally constructed invariant sheaf restricts to the invariant
sheaf of the restricted descent datum. -/
def invariantSheafRestrictIso (D : BeckDescent.SheafDatum f) :
    (Scheme.Modules.restrictFunctor U.ι).obj (BeckDescent.invariantSheaf f D) ≅
      BeckDescent.invariantSheaf (f ∣_ U) ((restrictDatum f U).obj D) := by
  have := ModuleLocality.restrict_preservesFiniteLimits U.ι
  have := Adjunction.rightMate_isIso f U
  exact InvariantRestriction.invariantRestrictionIso
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
    (Adjunction.adjointPullbackSquare f U) D

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.Descent
