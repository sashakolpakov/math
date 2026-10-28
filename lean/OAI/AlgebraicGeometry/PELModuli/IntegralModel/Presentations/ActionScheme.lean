import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.BoundedActionFunctor
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Parameter
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RepresentedSubfunctor

/-! # Action Scheme -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.ActionScheme

noncomputable section

/-! Apply the full corrected Presentations input to the actual primitive-generator
equations. This constructs a separated finite-type parameter scheme with an
actual universal integral action and its arbitrary-test-scheme classification.
The bound remains exactly Presentations's geometric graph Hilbert polynomial. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {S : Scheme} [IsLocallyNoetherian S] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)

theorem exists_e34_bounded_integral_action_scheme
    (hPresentations : Hilbert.EndomorphismEquationsInput.{0})
    (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A.scheme)
    (hc : ∀ s : S, IsUnit (D.conductor : S.presheaf.stalk s)) (P : Fin 1 → Polynomial ℚ) :
    ∃ (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.scheme ⨯ A.scheme))
      (L : HilbertScheme.Presentations.Loci.Core.HilbertHomLoci A.scheme A.scheme B 1 P)
      (M : HilbertScheme.Presentations.Loci.Core.EndomorphismEquationLoci A.scheme B 1 P L (Generator.EndomorphismFamilies.e34IntegralGeneratorEquations A D hc)),
      HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BA BA B ∧
      LocallyOfFiniteType M.solutionScheme.hom ∧ QuasiCompact M.solutionScheme.hom ∧
      IsSeparated M.solutionScheme.hom ∧
      ∃ ρZ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback M.solutionScheme.hom),
        HilbertScheme.Presentations.Has.Core.HasGraphPolynomials A.scheme A.scheme 1 B P
          ((HilbertScheme.Presentations.Endomorphisms.Core.forgetGroupLaw A.scheme 1).app (op M.solutionScheme)
            ((Integral.ActionFunctor.integralGeneratorTupleMap A D).app (op M.solutionScheme) ρZ)) ∧
        ∀ (T : Over S)
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback T.hom)),
          HilbertScheme.Presentations.Has.Core.HasGraphPolynomials A.scheme A.scheme 1 B P
            ((HilbertScheme.Presentations.Endomorphisms.Core.forgetGroupLaw A.scheme 1).app (op T) ((Integral.ActionFunctor.integralGeneratorTupleMap A D).app (op T) ρ)) ↔
              ∃! f : T ⟶ M.solutionScheme, Integral.ActionScheme.restrictIntegralAction A ρZ f = ρ := by
  obtain ⟨B, L, hseg, ⟨M⟩⟩ := hPresentations A.scheme BA 1 P (Generator.EndomorphismFamilies.e34IntegralGeneratorEquations A D hc)
  obtain ⟨hft, hqc, hsep⟩ := Parameter.e34SolutionScheme_finiteType_separated A.scheme M
  let F := Integral.ActionFunctor.integralActionFunctor A E
  let Q := BoundedActionFunctor.boundedIntegralActions A D hc B P L M
  let e := BoundedActionFunctor.boundedIntegralActionRepresentation A D hc B P L M
  let ρZ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback M.solutionScheme.hom) :=
    RepresentedSubfunctor.representedSubfunctorUniversal F Q M.solutionScheme e
  refine ⟨B, L, M, hseg, hft, hqc, hsep, ρZ, ?_, ?_⟩
  · exact (BoundedActionFunctor.boundedIntegralActions_mem A D hc B P L M M.solutionScheme ρZ).mp
      (RepresentedSubfunctor.representedSubfunctorUniversal_mem F Q M.solutionScheme e)
  · intro T ρ
    exact (BoundedActionFunctor.boundedIntegralActions_mem A D hc B P L M T ρ).symm.trans
      (RepresentedSubfunctor.representedSubfunctorUniversal_classifies F Q M.solutionScheme e T ρ)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.ActionScheme
