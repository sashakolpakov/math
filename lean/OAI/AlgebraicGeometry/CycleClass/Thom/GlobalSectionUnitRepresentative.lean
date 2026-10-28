import OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary

/-! # Global Section Unit Representative -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions

noncomputable section

/-! A nonzero global regular section has an actual rational unit
representative on its full basic open of invertibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme) [IsIntegral X]

local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, Opens.mem_top _⟩⟩

variable (s : Γ(X, ⊤)) (hs : X.germToFunctionField ⊤ s ≠ 0)

include hs in
theorem basicOpen_nonempty : Nonempty (X.basicOpen s) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  rw [X.mem_basicOpen s (genericPoint X) (Opens.mem_top _)]
  change IsUnit (X.germToFunctionField ⊤ s)
  exact isUnit_iff_ne_zero.mpr hs

def sectionUnitRepresentative : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X (X.germToFunctionField ⊤ s) where
  domain := X.basicOpen s
  nonempty_domain := basicOpen_nonempty X s hs
  unit := (X.toRingedSpace.isUnit_res_basicOpen s).unit
  represents := by
    let : Nonempty (X.basicOpen s) := basicOpen_nonempty X s hs
    rw [(X.toRingedSpace.isUnit_res_basicOpen s).unit_spec]
    exact RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict (X := X) (X.basicOpen_le s) s

theorem sectionUnitRepresentative_domain : (sectionUnitRepresentative X s hs).domain = X.basicOpen s := rfl

theorem sectionUnitRepresentative_unit :
    (sectionUnitRepresentative X s hs).unit.val =
      X.presheaf.map (X.basicOpen_le s).hom.op s :=
  (X.toRingedSpace.isUnit_res_basicOpen s).unit_spec

end

end OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions
