import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.Units

/-! # Open Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.OpenUnits

noncomputable section

/-! Units on finitely many pulled-back affine opens descend to
one common scheme stage, using the actual open-restriction maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
theorem exists_limit_open_unit_stage {i : I} (V : (D.obj i).Opens) (hV : IsAffineOpen V)
    (u : Γ((opensCone D c i V).pt, ⊤)ˣ) :
    ∃ (k : Over i) (v : Γ((opensDiagram D i V).obj k, ⊤)ˣ),
      Units.map ((opensCone D c i V).π.app k).appTop.hom.toMonoidHom v = u := by
  let : ∀ k : Over i, IsAffine ((opensDiagram D i V).obj k) :=
    fun k => hV.preimage (D.map k.hom)
  let : ∀ {k l : Over i} (f : k ⟶ l), IsAffineHom ((opensDiagram D i V).map f) :=
    fun _ => isAffineHom_of_isAffine _
  exact InverseLimit.Units.exists_limit_unit_stage (opensDiagram D i V) (opensCone D c i V)
    (isLimitOpensCone D c hc i V) u

include hc in
theorem exists_finite_limit_open_units_stage {J : Type u} [Fintype J]
    {i : I} (V : J → (D.obj i).Opens) (hV : ∀ j, IsAffineOpen (V j))
    (u : ∀ j, Γ((opensCone D c i (V j)).pt, ⊤)ˣ) :
    ∃ (k : Over i) (v : ∀ j, Γ((opensDiagram D i (V j)).obj k, ⊤)ˣ),
      ∀ j, Units.map ((opensCone D c i (V j)).π.app k).appTop.hom.toMonoidHom (v j) = u j := by
  classical
  choose k v hv using fun j => exists_limit_open_unit_stage D c hc (V j) (hV j) (u j)
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  let f (j : J) : l ⟶ k j := (hl (by simp)).some
  refine ⟨l, fun j => Units.map ((opensDiagram D i (V j)).map (f j)).appTop.hom.toMonoidHom (v j), ?_⟩
  intro j
  apply Units.ext
  exact (InverseLimit.Units.coneSection_map (opensDiagram D i (V j)) (opensCone D c i (V j)) (f j) (v j).val).trans
    (congrArg Units.val (hv j))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.OpenUnits
