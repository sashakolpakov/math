import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Local Exactness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.LocalExactness.Cech

noncomputable section

/-! Exactness of additive sheaves follows from exact sections on arbitrarily small neighborhoods. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}} (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))

theorem sheafExact_of_locally_exact_sections
    (hlocal : ∀ (V : Opens X) (x : V), ∃ W : Opens X, W ≤ V ∧ x.val ∈ W ∧
      ∀ s : S.X₂.obj.obj (op W), S.g.hom.app (op W) s = 0 →
        ∃ t : S.X₁.obj.obj (op W), S.f.hom.app (op W) t = s) : S.Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  obtain ⟨U, hxU, s, rfl⟩ := S.X₂.presheaf.exists_germ_eq y
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g.hom
    (S.X₂.presheaf.germ U x hxU s) = 0 at hy
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hy
  obtain ⟨V, hxV, iVU, _, hEq⟩ := S.X₃.presheaf.germ_eq x hxU hxU
    (S.g.hom.app (op U) s) 0 (hy.trans (map_zero _).symm)
  have hzero : S.X₃.obj.map iVU.op (S.g.hom.app (op U) s) = 0 := by
    rw [hEq, map_zero]
  obtain ⟨W, hWV, hxW, hW⟩ := hlocal V ⟨x, hxV⟩
  let iWU : W ⟶ U := homOfLE hWV ≫ iVU
  let sW := S.X₂.obj.map iWU.op s
  have hzeroW : S.X₃.obj.map iWU.op (S.g.hom.app (op U) s) = 0 := by
    change (S.X₃.obj.map (iVU.op ≫ (homOfLE hWV).op)) _ = 0
    rw [S.X₃.obj.map_comp]
    change S.X₃.obj.map (homOfLE hWV).op (S.X₃.obj.map iVU.op _) = 0
    rw [hzero, map_zero]
  have hsW : S.g.hom.app (op W) sW = 0 := by
    have h := congrArg (fun f : S.X₂.obj.obj (op U) ⟶ S.X₃.obj.obj (op W) => f.hom s)
      (S.g.hom.naturality iWU.op)
    exact h.trans hzeroW
  obtain ⟨t, ht⟩ := hW sW hsW
  refine ⟨S.X₁.presheaf.germ W x hxW t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f.hom
    (S.X₁.presheaf.germ W x hxW t) = S.X₂.presheaf.germ U x hxU s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht]
  exact S.X₂.presheaf.germ_res_apply iWU x hxW s

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.LocalExactness.Cech
