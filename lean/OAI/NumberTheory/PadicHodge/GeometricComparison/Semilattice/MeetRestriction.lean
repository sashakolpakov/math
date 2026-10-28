import Mathlib.Order.LatticeIntervals
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Meet Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MeetRestriction.SemilatticeMeetRestriction

noncomputable section

/-! Intersecting with a fixed element is the right adjoint to the inclusion
of its lower interval. The coefficient comparison uses the actual inclusions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w
variable (C : Type u) [SemilatticeInf C] (I : C)

def inclusion : Set.Iic I ⥤ C where
  obj V := V.val
  map α := homOfLE (leOfHom α)

def restriction : C ⥤ Set.Iic I where
  obj V := ⟨V ⊓ I, inf_le_right⟩
  map α := homOfLE (inf_le_inf_right I (leOfHom α))

def counit : restriction C I ⋙ inclusion C I ⟶ 𝟭 C where
  app _ := homOfLE inf_le_left

def adjunction : inclusion C I ⊣ restriction C I :=
  Adjunction.mkOfUnitCounit
    { unit := { app V := homOfLE (le_inf le_rfl V.property) }
      counit := SemilatticeMeetRestriction.counit C I }

instance preservesLimits : PreservesLimits (restriction C I) :=
  (adjunction C I).rightAdjoint_preservesLimits

variable {A : Type v} [Category.{w} A] (P : Cᵒᵖ ⥤ A)

def comparison : P ⟶ (restriction C I).op ⋙ (inclusion C I).op ⋙ P where
  app V := P.map (homOfLE (inf_le_left : V.unop ⊓ I ≤ V.unop)).op
  naturality U V α := by
    change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
    exact (P.map_comp _ _).symm.trans
      ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _))

variable (h : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

include h in
theorem comparison_isIso : IsIso (comparison C I P) := by
  let (V : Cᵒᵖ) : IsIso ((comparison C I P).app V) := h V.unop
  exact NatIso.isIso_of_isIso_app _

def iso : P ≅ (restriction C I).op ⋙ (inclusion C I).op ⋙ P := by
  let := comparison_isIso C I P h
  exact asIso (comparison C I P)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MeetRestriction.SemilatticeMeetRestriction
