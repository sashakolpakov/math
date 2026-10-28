import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Generator
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientProjectivePresentation

/-! # Generator Equation Sources -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.GeneratorEquationSources

noncomputable section

/-! The finite primitive-generator equations use actual projective
sources: the abelian family and its closed torsion subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Generator OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Generator.EndomorphismFamilies

theorem integralGeneratorEquations_projective_sources
    {S : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A.scheme)
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : PELModuli.IntegralModel.CM.GeneratorReconstruction.CMIntegralGeneratorData E) (hc : ∀ x : S, IsUnit (D.conductor : S.presheaf.stalk x)) :
    ∀ r ∈ PELModuli.IntegralModel.Presentations.Generator.EndomorphismFamilies.e34IntegralGeneratorEquations A D hc,
      Nonempty (HilbertScheme.Presentations.Has.Core.ProjectivePresentation r.source) := by
  intro r hr
  rcases List.mem_cons.mp hr with h | h
  · subst r
    exact ⟨BA⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    exact ⟨@HilbertScheme.Presentations.Has.Core.ProjectivePresentation.precompose S
      (A.torsionScheme D.conductor) A.scheme (A.torsionInclusion D.conductor)
      (HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionInclusion_closedImmersion A D.conductor) BA⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.GeneratorEquationSources
