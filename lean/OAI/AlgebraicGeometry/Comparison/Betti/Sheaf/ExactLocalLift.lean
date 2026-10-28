import OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkExactFunctor
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Exact Local Lift -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ExactLocalLift.Godement

noncomputable section

/-! Exactness of the actual sheaf sequence gives local lifts of its
closed sections, by representing and comparing their genuine stalk elements. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Presheaf

variable {X : TopCat.{0}} (S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X))

theorem local_section_lift_of_exact (hS : S.Exact) (U : Opens X)
    (s : S.X₂.obj.obj (op U)) (hs : S.g.hom.app (op U) s = 0) (x : U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x.val ∈ V ∧
      ∃ t : S.X₁.obj.obj (op V),
        S.f.hom.app (op V) t = S.X₂.obj.map (homOfLE hVU).op s := by
  have hex := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp hS x.val
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hz : (stalkFunctor (ModuleCat.{0} ℂ) x.val).map S.g.hom
      (germ S.X₂.obj U x.val x.property s) = 0 := by
    rw [stalkFunctor_map_germ_apply, hs, map_zero]
    rfl
  obtain ⟨t, ht⟩ := hex (germ S.X₂.obj U x.val x.property s) hz
  obtain ⟨W, hxW, a, rfl⟩ := exists_germ_eq S.X₁.obj t
  change (stalkFunctor (ModuleCat.{0} ℂ) x.val).map S.f.hom (germ S.X₁.obj W x.val hxW a) = _ at ht
  rw [stalkFunctor_map_germ_apply] at ht
  obtain ⟨V, hxV, iVW, iVU, hEq⟩ := germ_eq S.X₂.obj x.val hxW x.property
    (S.f.hom.app (op W) a) s ht
  refine ⟨V, leOfHom iVU, hxV, S.X₁.obj.map iVW.op a, ?_⟩
  have hnat := ConcreteCategory.congr_hom (S.f.hom.naturality iVW.op) a
  exact hnat.trans hEq

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ExactLocalLift.Godement
