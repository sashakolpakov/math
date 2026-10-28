import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechShort
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict

/-! # Ordinary Cech One -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrdinaryCechOne

noncomputable section

/-! The value of geometric pullback in ordinary Cech coordinates commutes
with both low-degree differentials, for arbitrary base morphisms. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.OrdinaryCechPullbackValues

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T)
variable (M : X.Modules) {ι : Type u} (U : ι → X.Opens)

abbrev source := CechShort.Construction.CechShortCoordinates.target π M U
abbrev target := CechShort.Construction.CechShortCoordinates.target ρ ((Scheme.Modules.pullback f).obj M) (fun i => f ⁻¹ᵁ U i)

def zero (z : (source π M U).X₁) : (target f ρ M U).X₁ :=
  fun i => PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (U i) (z i)

def one (z : (source π M U).X₂) : (target f ρ M U).X₂ :=
  fun i j => PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (U i ⊓ U j) (z i j)

def two (z : (source π M U).X₃) : (target f ρ M U).X₃ :=
  fun i j k => PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M ((U i ⊓ U j) ⊓ U k) (z i j k)

theorem differential_zero (z : (source π M U).X₁) :
    one f π ρ M U ((source π M U).f z) = (target f ρ M U).f (zero f π ρ M U z) := by
  funext i j
  change PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (U i ⊓ U j)
    (M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (z j) -
      M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (z i)) = _
  rw [map_sub, PullbackSectionRestrict.Construction.PullbackSectionCoefficients.restrict, PullbackSectionRestrict.Construction.PullbackSectionCoefficients.restrict]
  rfl

theorem differential_one (z : (source π M U).X₂) :
    two f π ρ M U ((source π M U).g z) = (target f ρ M U).g (one f π ρ M U z) := by
  funext i j k
  change PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M ((U i ⊓ U j) ⊓ U k)
    (M.presheaf.map (homOfLE (inf_le_left : (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j)).op (z i j) +
      M.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k)).op (z j k) -
      M.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k)).op (z i k)) = _
  rw [map_sub, map_add, PullbackSectionRestrict.Construction.PullbackSectionCoefficients.restrict, PullbackSectionRestrict.Construction.PullbackSectionCoefficients.restrict,
    PullbackSectionRestrict.Construction.PullbackSectionCoefficients.restrict]
  rfl

end Construction.OrdinaryCechPullbackValues

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrdinaryCechOne
