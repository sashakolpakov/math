import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSectionModules
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Sheaf Overlap Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SheafOverlapEquivalence

noncomputable section

/-! A module sheaf identifies its global sections with tuples of open-cover sections that agree on pairwise intersections. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : TopCat.Presheaf (ModuleCat.{u} R) X) {ι : Type v} (U : ι → Opens X)

def compatibleOpenSectionModule : Submodule R ((i : ι) → F.obj (op (U i))) where
  carrier := {s | ∀ i j, F.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (s i) =
    F.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (s j)}
  zero_mem' := by intro i j; simp only [Pi.zero_apply, map_zero]
  add_mem' := by intro x y hx hy i j; simp only [Pi.add_apply, map_add, hx i j, hy i j]
  smul_mem' := by intro r x hx i j; simp only [Pi.smul_apply, map_smul, hx i j]

def globalOpenSectionRestriction : F.obj (op ⊤) →ₗ[R] compatibleOpenSectionModule F U :=
  (LinearMap.pi (fun i => (F.map (homOfLE (show U i ≤ ⊤ from le_top)).op).hom)).codRestrict _ (by
    intro x i j
    change (F.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op)
        ((F.map (homOfLE (show U i ≤ ⊤ from le_top)).op) x) =
      (F.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op)
        ((F.map (homOfLE (show U j ≤ ⊤ from le_top)).op) x)
    simp only [← ConcreteCategory.comp_apply, ← F.map_comp]
    rfl)

theorem globalOpenSectionRestriction_bijective (hF : F.IsSheaf) (hU : iSup U = ⊤) :
    Function.Bijective (globalOpenSectionRestriction F U) := by
  let G : TopCat.Sheaf (ModuleCat.{u} R) X := ⟨F, hF⟩
  have cover : (⊤ : Opens X) ≤ iSup U := hU.ge
  constructor
  · intro x y hxy
    let s := globalOpenSectionRestriction F U x
    obtain ⟨z, _, hz⟩ := G.existsUnique_gluing' U ⊤ (fun i => (U i).leTop) cover s.val s.property
    apply (hz x (fun _ => rfl)).trans
    apply (hz y ?_).symm
    intro i
    exact (congrArg (fun t : compatibleOpenSectionModule F U => t.val i) hxy).symm
  · intro s
    obtain ⟨z, hz, _⟩ := G.existsUnique_gluing' U ⊤ (fun i => (U i).leTop) cover s.val s.property
    exact ⟨z, Subtype.ext (funext hz)⟩

def globalOpenSectionEquiv (hF : F.IsSheaf) (hU : iSup U = ⊤) :
    F.obj (op ⊤) ≃ₗ[R] compatibleOpenSectionModule F U :=
  LinearEquiv.ofBijective (globalOpenSectionRestriction F U) (globalOpenSectionRestriction_bijective F U hF hU)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SheafOverlapEquivalence
