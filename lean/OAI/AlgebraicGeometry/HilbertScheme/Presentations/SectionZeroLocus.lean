import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EquationLoci
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Section Zero Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionZeroLocus

noncomputable section

/-!
Simultaneous vanishing of global sections is a closed representable
condition over an arbitrary base scheme.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) {ι : Type u}

def sectionEquation (s : ι → Γ(M.left, ⊤)) : EquationLoci.MorphismEquation M where
  target := Over.mk (AffineSpace ι S ↘ S)
  separated := IsSeparated.of_isAffineHom (AffineSpace ι S ↘ S)
  lhs := Over.homMk (AffineSpace.homOfVector M.hom s) (AffineSpace.homOfVector_over _ _)
  rhs := Over.homMk (AffineSpace.homOfVector M.hom (fun _ => 0))
    (AffineSpace.homOfVector_over _ _)

theorem sectionEquation_satisfies (s : ι → Γ(M.left, ⊤)) {T : Over S} (x : T ⟶ M) :
    EquationLoci.Satisfies [sectionEquation M s] x ↔ ∀ i, x.left.appTop (s i) = 0 := by
  have hsimp : EquationLoci.Satisfies [sectionEquation M s] x ↔
      x ≫ (sectionEquation M s).lhs = x ≫ (sectionEquation M s).rhs := by
    simp only [EquationLoci.Satisfies, List.mem_singleton, forall_eq]
  rw [hsimp]
  constructor
  · intro h i
    have hcoord := congrArg (fun f : T ⟶ (sectionEquation M s).target =>
      f.left.appTop (AffineSpace.coord S i)) h
    change x.left.appTop ((AffineSpace.homOfVector M.hom s).appTop (AffineSpace.coord S i)) =
      x.left.appTop ((AffineSpace.homOfVector M.hom (fun _ : ι => 0)).appTop
        (AffineSpace.coord S i)) at hcoord
    simpa only [AffineSpace.homOfVector_appTop_coord, map_zero] using hcoord
  · intro h
    apply (Over.forget S).map_injective
    apply AffineSpace.hom_ext
    · exact (x ≫ (sectionEquation M s).lhs).w.trans (x ≫ (sectionEquation M s).rhs).w.symm
    · intro i
      change x.left.appTop ((AffineSpace.homOfVector M.hom s).appTop (AffineSpace.coord S i)) =
        x.left.appTop ((AffineSpace.homOfVector M.hom (fun _ : ι => 0)).appTop
          (AffineSpace.coord S i))
      simpa only [AffineSpace.homOfVector_appTop_coord, map_zero] using h i

def sectionZeroSubfunctor (s : ι → Γ(M.left, ⊤)) : Subfunctor (yoneda.obj M) where
  obj T := {x | ∀ i, x.left.appTop (s i) = 0}
  map a x hx := by
    intro i
    change a.unop.left.appTop (x.left.appTop (s i)) = 0
    rw [hx i, map_zero]

theorem section_zero_locus_representable (s : ι → Γ(M.left, ⊤)) :
    ∃ (Z : Over S) (j : Z ⟶ M), IsClosedImmersion j.left ∧
      ∃ e : yoneda.obj Z ≅ (sectionZeroSubfunctor M s).toFunctor,
        e.hom ≫ (sectionZeroSubfunctor M s).ι = yoneda.map j := by
  have hsub : EquationLoci.equationSubfunctor [sectionEquation M s] = sectionZeroSubfunctor M s := by
    ext T x
    exact sectionEquation_satisfies M s x
  have h := EquationLoci.finite_equations_representable [sectionEquation M s]
  rw [hsub] at h
  exact h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionZeroLocus
