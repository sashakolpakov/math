import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.GraphClassifierNaturality

/-! # Embedded Morphism Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.EmbeddedMorphismRepresentation

noncomputable section

/-! The functor of actual morphisms with a prescribed embedded graph polynomial has an actual quasi-projective representing scheme over a noetherian base, on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ}
variable [IsProper A.hom] [Smooth A.hom] [IsSeparated B.hom]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

def boundedEmbeddedMorphismClassifyingIso :
    EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P ≅ yoneda.obj (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P) :=
  NatIso.ofComponents (fun T => (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv j P T.unop).symm.toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro p
    change HilbertConstruction.Smooth.GraphClassifierLift.smoothEmbeddedGraphParameterClassifier j P ((EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P).map f p) =
      f.unop ≫ HilbertConstruction.Smooth.GraphClassifierLift.smoothEmbeddedGraphParameterClassifier j P p
    exact GraphClassifierNaturality.smoothEmbeddedGraphParameterClassifier_natural j P f.unop p)

theorem boundedEmbeddedMorphism_isRepresentable : (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P).IsRepresentable :=
  Functor.IsRepresentable.mk' (boundedEmbeddedMorphismClassifyingIso j P).symm

theorem boundedEmbeddedMorphism_quasiProjective_representation :
    ∃ M : Over S, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation M) ∧
      Nonempty (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P ≅ yoneda.obj M) :=
  ⟨HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P, ⟨HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameterQuasiProjectivePresentation j P⟩,
    ⟨boundedEmbeddedMorphismClassifyingIso j P⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.EmbeddedMorphismRepresentation
