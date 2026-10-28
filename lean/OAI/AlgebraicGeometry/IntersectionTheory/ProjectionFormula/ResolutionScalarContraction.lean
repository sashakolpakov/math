import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Resolution Scalar Contraction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionScalarContraction

noncomputable section

/-! A scalar annihilating the resolved module acts null-homotopically
on its actual projective resolution. The endpoint identities give the
auxiliary lift and the injectivity test needed after scalar extension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
  (r : R) (hr : ∀ x : M, r • x = 0)

include hr

def homotopy : Homotopy (r • 𝟙 P.complex) 0 := by
  apply ProjectiveResolution.liftHomotopyZero (P := P) (Q := P) (r • 𝟙 P.complex)
  rw [Linear.smul_comp, Category.id_comp]
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact hr (P.π.f 0 x)
  | succ n =>
    have hz : IsZero (((ChainComplex.single₀ (ModuleCat R)).obj M).X (n + 1)) :=
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    exact hz.eq_of_tgt _ _

def lift : P.complex.X 0 ⟶ P.complex.X 1 := (homotopy R M P r hr).hom 0 1

theorem lift_comp : lift R M P r hr ≫ P.complex.d 1 0 = r • 𝟙 (P.complex.X 0) := by
  have he := (homotopy R M P r hr).comm 0
  simpa only [lift, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
    HomologicalComplex.zero_f, Homotopy.dNext_zero_chainComplex,
    Homotopy.prevD_chainComplex, zero_add, add_zero] using he.symm

theorem top_comp (n : ℕ) (hn : IsZero (P.complex.X (n + 2))) :
    P.complex.d (n + 1) n ≫ (homotopy R M P r hr).hom n (n + 1) =
      r • 𝟙 (P.complex.X (n + 1)) := by
  have he := (homotopy R M P r hr).comm (n + 1)
  have hz : (homotopy R M P r hr).hom (n + 1) (n + 2) = 0 := hn.eq_of_tgt _ _
  simpa only [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
    HomologicalComplex.zero_f, Homotopy.dNext_succ_chainComplex,
    Homotopy.prevD_chainComplex, hz, zero_comp, add_zero] using he.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionScalarContraction
