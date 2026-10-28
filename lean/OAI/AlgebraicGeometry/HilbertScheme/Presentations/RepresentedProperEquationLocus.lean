import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ProperEquationLoci
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedSubfunctorRange

/-! # Represented Proper Equation Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedProperEquationLocus.Core

noncomputable section

/-! Restrict an already represented subfunctor by finite equations with
proper flat sources, retaining its exact values and inclusion transformation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
variable {M : Over S} [IsLocallyNoetherian M.left]

theorem represented_proper_equation_locus (G : Subfunctor F)
    (e : yoneda.obj M ≅ G.toFunctor) (R : List (Endomorphisms.Core.FamilyMorphismEquation F)) :
    ∃ (Z : Over S) (j : Z ⟶ M), IsClosedImmersion j.left ∧
      ∃ e' : yoneda.obj Z ≅ (G ⊓ Endomorphisms.Core.solutionSubfunctor R).toFunctor,
        e'.hom ≫ (G ⊓ Endomorphisms.Core.solutionSubfunctor R).ι = yoneda.map j ≫ e.hom ≫ G.ι := by
  obtain ⟨Z, j, hj, htest⟩ := Finite.ProperEquationLoci.Core.finite_proper_equations_closed_lifts R (e.hom ≫ G.ι)
  let : IsClosedImmersion j.left := hj
  let : Mono j := Over.mono_of_mono_left j
  refine ⟨Z, j, hj, ?_⟩
  apply RepresentedSubfunctorRange.representedSubfunctor_restrict G (Endomorphisms.Core.solutionSubfunctor R) e j
  intro T x
  constructor
  · intro hx
    exact ((htest T x).mp hx).exists
  · rintro ⟨y, hy⟩
    exact (htest T x).mpr ⟨y, hy, fun z hz => (cancel_mono j).mp (hz.trans hy.symm)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedProperEquationLocus.Core
