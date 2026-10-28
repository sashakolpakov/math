import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PeriodSequence
import Mathlib.Topology.Sheaves.Stalks

/-! # Sheaf Local Exact -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SheafLocalExact

noncomputable section

section

/-! Sectionwise exactness implies exactness of actual abelian sheaves, proved by local representatives of germs. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem abelianSheaf_exact_of_section_exact (X : TopCat.{0})
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
    (h : ∀ U : Opens X, (S.map
      (Holomorphic.PeriodSequence.abelianSheafSections X U)).Exact) : S.Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro z hz
  obtain ⟨U, hx, g, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.obj z
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g.hom
    (TopCat.Presheaf.germ S.X₂.obj U x hx g) = 0 at hz
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hz
  have hzero : TopCat.Presheaf.germ S.X₃.obj U x hx (S.g.hom.app (op U) g) =
      TopCat.Presheaf.germ S.X₃.obj U x hx 0 := by
    simpa only [map_zero] using hz
  obtain ⟨V, hxV, i, j, hr⟩ := TopCat.Presheaf.germ_eq S.X₃.obj x hx hx (S.g.hom.app (op U) g) 0 hzero
  have hv : S.g.hom.app (op V) (S.X₂.obj.map i.op g) = 0 := by
    have hn := ConcreteCategory.congr_hom (S.g.hom.naturality i.op) g
    simp only [ConcreteCategory.comp_apply] at hn
    rw [map_zero] at hr
    exact hn.trans hr
  obtain ⟨n, hn⟩ := (ShortComplex.ab_exact_iff _).mp (h V) (S.X₂.obj.map i.op g) hv
  refine ⟨TopCat.Presheaf.germ S.X₁.obj V x hxV n, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f.hom
    (TopCat.Presheaf.germ S.X₁.obj V x hxV n) = TopCat.Presheaf.germ S.X₂.obj U x hx g
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change S.f.hom.app (op V) n = S.X₂.obj.map i.op g at hn
  rw [hn]
  exact TopCat.Presheaf.germ_res_apply S.X₂.obj i x hxV g

end

/-! Local lifting of closed sections proves exactness of the original abelian sheaves. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem abelianSheaf_exact_of_local_lifts (X : TopCat.{0})
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
    (h : ∀ (U : Opens X) (s : S.X₂.obj.obj (op U)), S.g.hom.app (op U) s = 0 →
      ∀ x ∈ U, ∃ V : Opens X, x ∈ V ∧ ∃ hVU : V ≤ U,
        ∃ t : S.X₁.obj.obj (op V),
          S.f.hom.app (op V) t = S.X₂.obj.map (homOfLE hVU).op s) : S.Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro z hz
  obtain ⟨U, hx, g, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.obj z
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g.hom
    (TopCat.Presheaf.germ S.X₂.obj U x hx g) = 0 at hz
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hz
  have hzero : TopCat.Presheaf.germ S.X₃.obj U x hx (S.g.hom.app (op U) g) =
      TopCat.Presheaf.germ S.X₃.obj U x hx 0 := by
    simpa only [map_zero] using hz
  obtain ⟨V, hxV, i, j, hr⟩ := TopCat.Presheaf.germ_eq S.X₃.obj x hx hx (S.g.hom.app (op U) g) 0 hzero
  have hv : S.g.hom.app (op V) (S.X₂.obj.map i.op g) = 0 := by
    have hn := ConcreteCategory.congr_hom (S.g.hom.naturality i.op) g
    simp only [ConcreteCategory.comp_apply] at hn
    rw [map_zero] at hr
    exact hn.trans hr
  obtain ⟨W, hxW, hWV, t, ht⟩ := h V (S.X₂.obj.map i.op g) hv x hxV
  refine ⟨TopCat.Presheaf.germ S.X₁.obj W x hxW t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f.hom
    (TopCat.Presheaf.germ S.X₁.obj W x hxW t) = TopCat.Presheaf.germ S.X₂.obj U x hx g
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht]
  exact (TopCat.Presheaf.germ_res_apply S.X₂.obj (homOfLE hWV) x hxW (S.X₂.obj.map i.op g)).trans
    (TopCat.Presheaf.germ_res_apply S.X₂.obj i x hxV g)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SheafLocalExact
