import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterRestriction
import Mathlib.RingTheory.KrullDimension.PID

/-! # Parameter Dominance -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterDominance

noncomputable section

/-! A nonzero parameter germ at a point of its scalar fiber forces
an integral support to dominate the parameter line. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry IsLocalRing
open scoped _root_.Polynomial

variable {Z : Scheme} [IsIntegral Z] (t : Z ⟶ Spec (.of ℂ[X]))

theorem germ_generic (x : Z) (a : ℂ) :
    algebraMap (Z.presheaf.stalk x) Z.functionField (ParameterFiber.germ ℂ t x a) =
      ParameterFiber.germ ℂ t (genericPoint Z) a := by
  have hx := GermPullback.appLE t ⊤ ⊤ le_top x trivial
    ((Scheme.ΓSpecIso (.of ℂ[X])).inv (Polynomial.X - Polynomial.C a))
  have hη := GermPullback.appLE t ⊤ ⊤ le_top (genericPoint Z) trivial
    ((Scheme.ΓSpecIso (.of ℂ[X])).inv (Polynomial.X - Polynomial.C a))
  change ParameterFiber.germ ℂ t x a = _ at hx
  change ParameterFiber.germ ℂ t (genericPoint Z) a = _ at hη
  rw [hx, hη]
  change (Z.presheaf.germ ⊤ x trivial ≫ Z.presheaf.stalkSpecializes
    ((genericPoint_spec Z).specializes trivial)) _ = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

theorem generic (x : Z) (a : ℂ) (hx : t x = ParameterFiber.point ℂ a)
    (hreg : ParameterFiber.germ ℂ t x a ≠ 0) :
    t (genericPoint Z) = genericPoint (Spec (.of ℂ[X])) := by
  let q := t (genericPoint Z)
  by_cases hq : q.asIdeal = ⊥
  · rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hq
  have hmax : q.asIdeal.IsMaximal := q.isPrime.isMaximal_of_ne_bot hq
  have hle : q.asIdeal ≤ (t x).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).mpr
    (((genericPoint_spec Z).specializes trivial).map t.continuous)
  have he : q = t x := PrimeSpectrum.ext (hmax.eq_of_le (t x).isPrime.ne_top hle)
  have hz := (ParameterFiber.germ_mem_maximalIdeal ℂ t (genericPoint Z) a).mpr (he.trans hx)
  have hg : ParameterFiber.germ ℂ t (genericPoint Z) a = 0 := by
    rw [maximalIdeal_eq_bot] at hz
    exact hz
  apply False.elim
  apply hreg
  apply IsFractionRing.injective (Z.presheaf.stalk x) Z.functionField
  rw [map_zero, germ_generic, hg]

theorem projective_generic (x : Z) (a : ℂ) (hx : t x = ParameterFiber.point ℂ a)
    (hreg : ParameterFiber.germ ℂ t x a ≠ 0) :
    (t ≫ Projective.FamilyIs.MatrixParameterOpen.affine) (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) := by
  change Projective.FamilyIs.MatrixParameterOpen.affine (t (genericPoint Z)) = _
  rw [generic t x a hx hreg]
  exact genericPoint_eq_of_isOpenImmersion Projective.FamilyIs.MatrixParameterOpen.affine

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterDominance
