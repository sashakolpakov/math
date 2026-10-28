import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.Units

/-! # Unit Equations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.UnitEquations

noncomputable section

/-! Finitely many equations between actual regular units hold
simultaneously at one later stage of a directed inverse system. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})

theorem diagramUnitPullback_comp {i j k : I} (f : j ⟶ i) (g : k ⟶ j)
    (a : Γ(D.obj i, ⊤)ˣ) :
    Units.map (D.map (g ≫ f)).appTop.hom.toMonoidHom a =
      Units.map (D.map g).appTop.hom.toMonoidHom
        (Units.map (D.map f).appTop.hom.toMonoidHom a) := by
  apply Units.ext
  exact congrArg (fun h : D.obj k ⟶ D.obj i => h.appTop a.val) (D.map_comp g f)

variable (c : Cone D) (hc : IsLimit c) [IsCofiltered I] [Quiver.IsThin I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]

include hc in
theorem exists_finite_limit_unit_equations {J : Type u} [Fintype J]
    {i : I} (a b : J → Γ(D.obj i, ⊤)ˣ)
    (h : ∀ j, Units.map (c.π.app i).appTop.hom.toMonoidHom (a j) =
      Units.map (c.π.app i).appTop.hom.toMonoidHom (b j)) :
    ∃ (k : I) (f : k ⟶ i), ∀ j,
      Units.map (D.map f).appTop.hom.toMonoidHom (a j) =
        Units.map (D.map f).appTop.hom.toMonoidHom (b j) := by
  classical
  choose j f hf using fun x => InverseLimit.Units.exists_limit_units_equal_stage D c hc (a x) (b x) (h x)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (insert i (Finset.univ.image j))
  let g : k ⟶ i := (hk (Finset.mem_insert_self _ _)).some
  let w (x : J) : k ⟶ j x := (hk (by simp)).some
  refine ⟨k, g, ?_⟩
  intro x
  have hw : Units.map (D.map (w x ≫ f x)).appTop.hom.toMonoidHom (a x) =
      Units.map (D.map (w x ≫ f x)).appTop.hom.toMonoidHom (b x) :=
    (diagramUnitPullback_comp D (f x) (w x) (a x)).trans
      ((congrArg (Units.map (D.map (w x)).appTop.hom.toMonoidHom) (hf x)).trans
        (diagramUnitPullback_comp D (f x) (w x) (b x)).symm)
  have hg : w x ≫ f x = g := Subsingleton.elim _ _
  exact hg ▸ hw

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.UnitEquations
