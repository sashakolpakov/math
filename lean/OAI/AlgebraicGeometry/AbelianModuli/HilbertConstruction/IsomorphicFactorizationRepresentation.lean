import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicFactorizationNaturality

/-! # Isomorphic Factorization Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicFactorizationRepresentation

noncomputable section

/-! The original factorization-isomorphism subfunctor is represented by the constructed quasi-projective parameter locus on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {X P Z A : Over M.left}
variable [IsProper X.hom] [Flat X.hom] [IsProper A.hom]
variable (j : Z ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P) (p : Z ⟶ A)

def isomorphicFactorizationSubfunctor : Subfunctor (yoneda.obj M) where
  obj _ := {c | FactorizationPointCondition.HasIsomorphicFactorization j i p c.left}
  map f c hc := IsomorphicFactorizationNaturality.hasIsomorphicFactorization_precomp M j i p c hc f.unop

def isomorphicFactorizationClassifyingIso :
    yoneda.obj (FactorizationIsomorphismParameter.factorizationIsomorphismParameter M j i p) ≅
      (isomorphicFactorizationSubfunctor M j i p).toFunctor :=
  NatIso.ofComponents (fun T => (IsomorphicFactorizationPoints.isomorphicFactorizationPointEquiv M j i p T.unop).toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    exact IsomorphicFactorizationNaturality.isomorphicFactorizationPointEquiv_natural M j i p f.unop y)

theorem isomorphicFactorization_isRepresentable :
    (isomorphicFactorizationSubfunctor M j i p).toFunctor.IsRepresentable :=
  Functor.IsRepresentable.mk' (isomorphicFactorizationClassifyingIso M j i p)

theorem isomorphicFactorization_quasiProjective_representation [IsNoetherian S]
    (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation M) :
    ∃ B : Over S, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation B) ∧
      Nonempty ((isomorphicFactorizationSubfunctor M j i p).toFunctor ≅ yoneda.obj B) :=
  ⟨FactorizationIsomorphismParameter.factorizationIsomorphismParameter M j i p,
    ⟨FactorizationIsomorphismParameter.factorizationIsomorphismParameterQuasiProjectivePresentation M j i p Q⟩,
    ⟨(isomorphicFactorizationClassifyingIso M j i p).symm⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicFactorizationRepresentation
