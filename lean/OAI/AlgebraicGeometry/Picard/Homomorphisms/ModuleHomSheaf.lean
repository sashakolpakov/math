import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.Topology.Sheaves.Sheaf

/-! # Module Hom Sheaf -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomSheaf

noncomputable section

/-! The sheaf of locally defined linear maps between actual module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} (M N : X.Modules)

def IsLinearLocalHom {U : X.Opens}
    (a : (presheafHom M.presheaf N.presheaf).obj (.op U)) : Prop :=
  ∀ (V : Over U) (r : Γ(X, V.left)) (s : Γ(M, V.left)),
    a.app (.op V) (r • s) = r • (show Γ(N, V.left) from a.app (.op V) s)

def linearHomSubfunctor : Subfunctor (presheafHom M.presheaf N.presheaf) where
  obj U := {a | IsLinearLocalHom M N a}
  map {U V} f a ha := by
    intro W r s
    exact ha ((Over.map f.unop).obj W) r s

theorem linearHomSubfunctor_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (linearHomSubfunctor M N).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply ((linearHomSubfunctor M N).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type _ _).mp (N.isSheaf.hom M.presheaf))).mpr
  intro U a ha V r s
  apply N.isSheaf.section_ext
  intro x hx
  obtain ⟨W, i, hi, hxW⟩ := ha x ((leOfHom V.hom) hx)
  let Z := V.left ⊓ W
  let z : Over U.unop := Over.mk (homOfLE (show Z ≤ U.unop from
    inf_le_left.trans (leOfHom V.hom)))
  let j : z ⟶ V := Over.homMk (homOfLE (show Z ≤ V.left from inf_le_left))
  have hn (t : Γ(M, V.left)) := ConcreteCategory.congr_hom (a.naturality j.op) t
  change ∀ t : Γ(M, V.left),
    a.app (.op z) (M.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op t) =
      N.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op (a.app (.op V) t) at hn
  have hl := hi (Over.mk (homOfLE (show Z ≤ W from inf_le_right)))
    (X.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op r)
    (M.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op s)
  refine ⟨Z, inf_le_left, ⟨hx, hxW⟩, ?_⟩
  change N.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op
      (a.app (.op V) (r • s)) =
    N.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op
      (r • (show Γ(N, V.left) from a.app (.op V) s))
  have hsm := N.val.map_smul (homOfLE (show Z ≤ V.left from inf_le_left)).op r
    (a.app (.op V) s)
  change N.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op
      (r • (show Γ(N, V.left) from a.app (.op V) s)) = _ at hsm
  erw [hsm, ← hn (r • s), ← hn s]
  erw [M.val.map_smul]
  exact hl

/-- Local module homomorphisms form a genuine sheaf, before any sheafification. -/
def linearHomSheaf : TopCat.Sheaf (Type u) X :=
  ⟨(linearHomSubfunctor M N).toFunctor, linearHomSubfunctor_isSheaf M N⟩

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomSheaf
