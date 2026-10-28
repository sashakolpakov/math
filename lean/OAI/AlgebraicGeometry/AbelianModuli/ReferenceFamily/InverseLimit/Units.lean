import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.Units

noncomputable section

/-! Actual invertible regular functions, including their inverse
equations, descend to a finite stage of a qcqs affine-transition limit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

theorem coneSection_map {i j : I} (f : j ⟶ i) (s : Γ(D.obj i, ⊤)) :
    (c.π.app j).appTop ((D.map f).appTop s) = (c.π.app i).appTop s := by
  exact congrArg (fun h : c.pt ⟶ D.obj i => h.appTop s) (c.w f)

variable (hc : IsLimit c) [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
theorem exists_limit_unit_stage (u : Γ(c.pt, ⊤)ˣ) :
    ∃ (i : I) (v : Γ(D.obj i, ⊤)ˣ),
      Units.map (c.π.app i).appTop.hom.toMonoidHom v = u := by
  obtain ⟨i, a, ha⟩ := exists_appTop_π_eq_of_isLimit D c hc u.val
  obtain ⟨j, b, hb⟩ := exists_appTop_π_eq_of_isLimit D c hc u.inv
  let k := IsCofiltered.min i j
  let a' := (D.map (IsCofiltered.minToLeft i j)).appTop a
  let b' := (D.map (IsCofiltered.minToRight i j)).appTop b
  have ha' : (c.π.app k).appTop a' = u.val :=
    (coneSection_map D c (IsCofiltered.minToLeft i j) a).trans ha.symm
  have hb' : (c.π.app k).appTop b' = u.inv :=
    (coneSection_map D c (IsCofiltered.minToRight i j) b).trans hb.symm
  have hz : (c.π.app k).appTop (a' * b' - 1) = 0 := by
    rw [map_sub, map_mul, map_one, ha', hb', u.val_inv, sub_self]
  obtain ⟨l, f, hf⟩ := exists_appTop_map_eq_zero_of_isLimit D c hc (a' * b' - 1) hz
  have hab : (D.map f).appTop a' * (D.map f).appTop b' = 1 :=
    sub_eq_zero.mp (by simpa only [map_sub, map_mul, map_one] using hf)
  let v : Γ(D.obj l, ⊤)ˣ :=
    ⟨(D.map f).appTop a', (D.map f).appTop b', hab, by rw [mul_comm]; exact hab⟩
  refine ⟨l, v, Units.ext ?_⟩
  exact (coneSection_map D c f a').trans ha'

include hc in
theorem exists_finite_limit_units_stage {J : Type u} [Fintype J]
    (u : J → Γ(c.pt, ⊤)ˣ) :
    ∃ (i : I) (v : J → Γ(D.obj i, ⊤)ˣ),
      ∀ j, Units.map (c.π.app i).appTop.hom.toMonoidHom (v j) = u j := by
  classical
  choose i v hv using fun j => exists_limit_unit_stage D c hc (u j)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let f (j : J) : k ⟶ i j := (hk (by simp)).some
  refine ⟨k, fun j => Units.map (D.map (f j)).appTop.hom.toMonoidHom (v j), ?_⟩
  intro j
  apply Units.ext
  exact (coneSection_map D c (f j) (v j).val).trans (congrArg Units.val (hv j))

omit [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
theorem exists_limit_units_equal_stage {i : I} (a b : Γ(D.obj i, ⊤)ˣ)
    (h : Units.map (c.π.app i).appTop.hom.toMonoidHom a =
      Units.map (c.π.app i).appTop.hom.toMonoidHom b) :
    ∃ (j : I) (f : j ⟶ i), Units.map (D.map f).appTop.hom.toMonoidHom a =
      Units.map (D.map f).appTop.hom.toMonoidHom b := by
  have hz : (c.π.app i).appTop (a.val - b.val) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Units.val h)
  obtain ⟨j, f, hf⟩ := exists_appTop_map_eq_zero_of_isLimit D c hc (a.val - b.val) hz
  refine ⟨j, f, Units.ext ?_⟩
  change (D.map f).appTop a.val = (D.map f).appTop b.val
  exact sub_eq_zero.mp (by simpa only [map_sub] using hf)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.Units
