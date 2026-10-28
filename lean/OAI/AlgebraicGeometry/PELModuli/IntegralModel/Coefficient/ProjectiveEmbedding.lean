import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.CoefficientReplacement
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Isomorphisms
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization

/-! # Projective Embedding -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.ProjectiveEmbedding.Coefficients

noncomputable section

/-! A generic closed embedding into a proper coefficient model becomes a
closed embedding after enlarging the finite coefficient ring. The source
remains the actual base change of the specified model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem coefficient_projective_embedding_after_enlargement
    {R K : Type} [CommRing R] [IsNoetherianRing R] [Field K] [Algebra R K]
    {s : Finset K} (M P : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s))
    (hM : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism M.hom) [IsProper P.hom] (f : M ⟶ P)
    [IsClosedImmersion ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).map f).left] :
    ∃ (t : Finset K) (h : s ⊆ t)
      (j : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj M ⟶
        (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj P), IsClosedImmersion j.left := by
  obtain ⟨N, j, hj, _, hN, ⟨e⟩⟩ := Proper.CoefficientReplacement.Coefficients.proper_coefficient_replacement M P f
  let g := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s
  obtain ⟨t, h, a, _⟩ := Isomorphisms.Coefficients.isomorphism_between_models_descends M N hM hN
    (pullback.fst M.hom g) (pullback.fst N.hom g)
    (IsPullback.of_hasPullback M.hom g) (IsPullback.of_hasPullback N.hom g) e.symm
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
  have : IsClosedImmersion j.left := hj
  have : IsClosedImmersion (F.map j).left := by
    exact MorphismProperty.of_isPullback (Specialization.base_change_square _ j) hj
  have : IsIso a.hom.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K t)).mapIso a).isIso_hom
  exact ⟨t, h, a.hom ≫ F.map j,
    inferInstanceAs (IsClosedImmersion (a.hom.left ≫ (F.map j).left))⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.ProjectiveEmbedding.Coefficients
