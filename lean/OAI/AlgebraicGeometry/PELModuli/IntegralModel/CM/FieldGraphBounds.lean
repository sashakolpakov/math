import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.GeometricFieldGraphBounds
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldGraphBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiRestriction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Field Graph Bounds -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM

noncomputable section

/-! Descend the fixed CM graph polynomial from algebraic closures to
arbitrary coefficient fields, including their actual restricted actions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem GeneratorReconstruction.CMIntegralGeneratorData.exists_uniform_field_graph_polynomial
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : GeneratorReconstruction.CMIntegralGeneratorData E)
    {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) :
    ∃ (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A.abelian.scheme) (Q : Polynomial ℚ),
      ∀ (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.abelian.scheme ⨯ A.abelian.scheme)),
        HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BA BA B →
        ∀ (K : Type) [Field K] (a : Spec (.of K) ⟶ Spec (.of k))
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback a).abelian),
          AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback a) ρ →
          HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
            (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B a (ρ.map D.generator)).ker).toIdeal Q := by
  classical
  obtain ⟨BA, Q, hQ⟩ := D.exists_uniform_geometric_field_graph_polynomial A
  refine ⟨BA, Q, fun B hB K _ a ρ hρ => ?_⟩
  let L := AlgebraicClosure K
  let β := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let b : Over.mk (β ≫ a) ⟶ Over.mk a := Over.homMk β rfl
  let σ := Integral.ActionScheme.restrictIntegralAction A.abelian ρ b
  have hσ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback (β ≫ a)) σ :=
    RosatiRestriction.rosati_restrictIntegralAction (T := Over.mk (β ≫ a)) (U := Over.mk a)
      (E := E) A ρ hρ b
  have hp := hQ B hB L (β ≫ a) σ hσ
  exact (FieldGraphBaseChange.PolarizationEmbedding.relativeIntegralGraph_hilbertPolynomial_baseChange_iff
    a (algebraMap K L) A.abelian B ρ D.generator Q).mp hp

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM
