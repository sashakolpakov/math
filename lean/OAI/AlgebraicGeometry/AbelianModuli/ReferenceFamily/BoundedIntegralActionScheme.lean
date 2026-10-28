import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.GeneratorEquationSources
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Hom
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.EndomorphismEquationPackage
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.BoundedActionFunctor
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Parameter
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RepresentedSubfunctor

/-! # Bounded Integral Action Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BoundedIntegralActionScheme

noncomputable section

/-! Construct the finite-type scheme of integral actions with a fixed
primitive-generator graph polynomial. Both relative Hom representability
and the required equation loci are supplied by proved projective-source
theorems. The resulting universal action classifies arbitrary test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

theorem exists_bounded_integral_action_scheme
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : PELModuli.IntegralModel.CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A.scheme)
    (hc : ∀ x : S, IsUnit (D.conductor : S.presheaf.stalk x)) (P : Fin 1 → Polynomial ℚ) :
    ∃ (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.scheme ⨯ A.scheme))
      (L : HilbertScheme.Presentations.Loci.Core.HilbertHomLoci A.scheme A.scheme B 1 P)
      (M : HilbertScheme.Presentations.Loci.Core.EndomorphismEquationLoci A.scheme B 1 P L (PELModuli.IntegralModel.Presentations.Generator.EndomorphismFamilies.e34IntegralGeneratorEquations A D hc)),
      HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BA BA B ∧
      LocallyOfFiniteType M.solutionScheme.hom ∧ QuasiCompact M.solutionScheme.hom ∧
      IsSeparated M.solutionScheme.hom ∧
      ∃ ρZ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback M.solutionScheme.hom),
        HilbertScheme.Presentations.Has.Core.HasGraphPolynomials A.scheme A.scheme 1 B P
          ((HilbertScheme.Presentations.Endomorphisms.Core.forgetGroupLaw A.scheme 1).app (op M.solutionScheme)
            ((PELModuli.IntegralModel.Integral.ActionFunctor.integralGeneratorTupleMap A D).app (op M.solutionScheme) ρZ)) ∧
        ∀ (T : Over S)
          (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback T.hom)),
          HilbertScheme.Presentations.Has.Core.HasGraphPolynomials A.scheme A.scheme 1 B P
            ((HilbertScheme.Presentations.Endomorphisms.Core.forgetGroupLaw A.scheme 1).app (op T) ((PELModuli.IntegralModel.Integral.ActionFunctor.integralGeneratorTupleMap A D).app (op T) ρ)) ↔
              ∃! f : T ⟶ M.solutionScheme, PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A ρZ f = ρ := by
  obtain ⟨B, hseg, ⟨L⟩⟩ := HilbertScheme.Presentations.Relative.Hom.Core.relative_hilbert_and_hom_loci A.scheme A.scheme BA BA 1 P
  obtain ⟨M⟩ := HilbertScheme.Presentations.Projective.EndomorphismEquationPackage.Core.endomorphismEquationLoci_of_projective_sources A.scheme BA L
    (PELModuli.IntegralModel.Presentations.Generator.EndomorphismFamilies.e34IntegralGeneratorEquations A D hc)
    (Integral.GeneratorEquationSources.integralGeneratorEquations_projective_sources A BA D hc)
  obtain ⟨hft, hqc, hsep⟩ := PELModuli.IntegralModel.Presentations.Parameter.e34SolutionScheme_finiteType_separated A.scheme M
  let F := PELModuli.IntegralModel.Integral.ActionFunctor.integralActionFunctor A E
  let Q := PELModuli.IntegralModel.Presentations.BoundedActionFunctor.boundedIntegralActions A D hc B P L M
  let e := PELModuli.IntegralModel.Presentations.BoundedActionFunctor.boundedIntegralActionRepresentation A D hc B P L M
  let ρZ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback M.solutionScheme.hom) :=
    PELModuli.IntegralModel.RepresentedSubfunctor.representedSubfunctorUniversal F Q M.solutionScheme e
  refine ⟨B, L, M, hseg, hft, hqc, hsep, ρZ, ?_, ?_⟩
  · exact (PELModuli.IntegralModel.Presentations.BoundedActionFunctor.boundedIntegralActions_mem A D hc B P L M M.solutionScheme ρZ).mp
      (PELModuli.IntegralModel.RepresentedSubfunctor.representedSubfunctorUniversal_mem F Q M.solutionScheme e)
  · intro T ρ
    exact (PELModuli.IntegralModel.Presentations.BoundedActionFunctor.boundedIntegralActions_mem A D hc B P L M T ρ).symm.trans
      (PELModuli.IntegralModel.RepresentedSubfunctor.representedSubfunctorUniversal_classifies F Q M.solutionScheme e T ρ)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BoundedIntegralActionScheme
