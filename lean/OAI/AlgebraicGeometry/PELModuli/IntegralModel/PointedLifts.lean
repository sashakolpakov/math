import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Lean.Util.CollectAxioms

/-! # Pointed Lifts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedLifts

noncomputable section

/-! Uniqueness of a pointed lift through a separated unramified morphism.
The equality locus is an actual open and closed pullback of the diagonal;
connectedness and the common base point force it to be the whole source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- A lift through a separated unramified finite-type map is determined
by one point on a connected source. -/
theorem pointed_unramified_lifts_unique
    {X Y Z W : Scheme.{u}} [ConnectedSpace X] [Nonempty W]
    (q : Y ⟶ Z) [FormallyUnramified q] [LocallyOfFiniteType q] [IsSeparated q]
    (f g : X ⟶ Y) (hcomp : f ≫ q = g ≫ q)
    (x₀ : W ⟶ X) (hpoint : x₀ ≫ f = x₀ ≫ g) : f = g := by
  let p : X ⟶ pullback q q := pullback.lift f g hcomp
  let d := pullback.diagonal q
  let E := pullback p d
  let e : E ⟶ X := pullback.fst p d
  have hpoint' : x₀ ≫ p = (x₀ ≫ f) ≫ d := by
    apply pullback.hom_ext
    · simp only [Category.assoc, p, d, pullback.lift_fst, pullback.diagonal_fst,
        Category.comp_id]
    · simp only [Category.assoc, p, d, pullback.lift_snd, pullback.diagonal_snd,
        Category.comp_id]
      exact hpoint.symm
  let z : W ⟶ E := pullback.lift x₀ (x₀ ≫ f) hpoint'
  have : IsOpenImmersion e := inferInstanceAs (IsOpenImmersion (pullback.fst p d))
  have : IsClosedImmersion e := inferInstanceAs (IsClosedImmersion (pullback.fst p d))
  have he : IsClopen (Set.range e) :=
    ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range e).Nonempty := ⟨e (z (Classical.arbitrary W)), Set.mem_range_self _⟩
  have hrange : Set.range e = Set.univ := he.eq_univ hne
  have : Surjective e := ⟨Set.range_eq_univ.mp hrange⟩
  have : IsIso e := (isIso_iff_isOpenImmersion_and_surjective e).mpr
    ⟨inferInstance, inferInstance⟩
  have h : e ≫ p = pullback.snd p d ≫ d := pullback.condition
  have hf := congrArg (fun k => k ≫ pullback.fst q q) h
  have hg := congrArg (fun k => k ≫ pullback.snd q q) h
  have hf' : e ≫ f = pullback.snd p d := by
    simpa only [Category.assoc, p, d, pullback.lift_fst, pullback.diagonal_fst,
      Category.comp_id] using hf
  have hg' : e ≫ g = pullback.snd p d := by
    simpa only [Category.assoc, p, d, pullback.lift_snd, pullback.diagonal_snd,
      Category.comp_id] using hg
  exact (cancel_epi e).mp (hf'.trans hg'.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedLifts
