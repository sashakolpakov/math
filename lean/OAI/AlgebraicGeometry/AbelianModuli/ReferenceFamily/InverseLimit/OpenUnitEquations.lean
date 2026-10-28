import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.OpenUnits
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.UnitEquations

/-! # Open Unit Equations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.OpenUnitEquations

noncomputable section

/-! Equations on finitely many distinct affine overlap opens become
simultaneously valid at one actual later coefficient stage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [IsCofiltered I] [Quiver.IsThin I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
theorem exists_finite_limit_open_unit_equations {J : Type u} [Fintype J]
    {i : I} (V : J → (D.obj i).Opens) (hV : ∀ j, IsAffineOpen (V j))
    (k : Over i) (a b : ∀ j, Γ((opensDiagram D i (V j)).obj k, ⊤)ˣ)
    (h : ∀ j, Units.map ((opensCone D c i (V j)).π.app k).appTop.hom.toMonoidHom (a j) =
      Units.map ((opensCone D c i (V j)).π.app k).appTop.hom.toMonoidHom (b j)) :
    ∃ (l : Over i) (f : l ⟶ k), ∀ j,
      Units.map ((opensDiagram D i (V j)).map f).appTop.hom.toMonoidHom (a j) =
        Units.map ((opensDiagram D i (V j)).map f).appTop.hom.toMonoidHom (b j) := by
  classical
  let : ∀ (j : J) (l : Over i), IsAffine ((opensDiagram D i (V j)).obj l) :=
    fun j l => (hV j).preimage (D.map l.hom)
  let : ∀ (j : J) {l m : Over i} (f : l ⟶ m), IsAffineHom ((opensDiagram D i (V j)).map f) :=
    fun j {l m} f => isAffineHom_of_isAffine ((opensDiagram D i (V j)).map f)
  have hs (j : J) := InverseLimit.Units.exists_limit_units_equal_stage (opensDiagram D i (V j))
    (opensCone D c i (V j)) (isLimitOpensCone D c hc i (V j)) (a j) (b j) (h j)
  choose l f hf using hs
  obtain ⟨m, hm⟩ := IsCofiltered.inf_objs_exists (insert k (Finset.univ.image l))
  let g : m ⟶ k := (hm (Finset.mem_insert_self _ _)).some
  let w (j : J) : m ⟶ l j := (hm (by simp)).some
  refine ⟨m, g, ?_⟩
  intro j
  have hw : Units.map ((opensDiagram D i (V j)).map (w j ≫ f j)).appTop.hom.toMonoidHom (a j) =
      Units.map ((opensDiagram D i (V j)).map (w j ≫ f j)).appTop.hom.toMonoidHom (b j) :=
    (UnitEquations.diagramUnitPullback_comp (opensDiagram D i (V j)) (f j) (w j) (a j)).trans
      ((congrArg (Units.map ((opensDiagram D i (V j)).map (w j)).appTop.hom.toMonoidHom) (hf j)).trans
        (UnitEquations.diagramUnitPullback_comp (opensDiagram D i (V j)) (f j) (w j) (b j)).symm)
  have hg : w j ≫ f j = g := by
    apply Over.OverMorphism.ext
    exact Subsingleton.elim _ _
  exact hg ▸ hw

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.OpenUnitEquations
