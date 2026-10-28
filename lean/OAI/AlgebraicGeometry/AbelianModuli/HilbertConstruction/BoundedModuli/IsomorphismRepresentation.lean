import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.PointEquivalence

/-! # Isomorphism Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.IsomorphismRepresentation

noncomputable section

/-! The complete bounded polarized full-level isomorphism functor is represented by the explicit quasi-projective intersection parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
variable (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme)

def boundedPolarizedLevelClassifyingIso :
    yoneda.obj (Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P) ≅ IsomorphismFunctor.boundedFamilyLevelIsoFunctor A B j P :=
  NatIso.ofComponents (fun T => (PointEquivalence.boundedPolarizedLevelIsoPointEquiv A B j P PB PD PE T.unop).toIso)
    (fun _ => (ClassifyingMap.boundedPolarizedLevelClassifyingMap A B j P PB PD PE).naturality _)

include PB PD PE in
theorem boundedPolarizedLevelIso_quasiProjective_representation :
    ∃ M : Over S, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation M) ∧
      Nonempty (IsomorphismFunctor.boundedFamilyLevelIsoFunctor A B j P ≅ yoneda.obj M) :=
  ⟨Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P,
    ⟨Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterQuasiProjectivePresentation A B j P⟩,
    ⟨(boundedPolarizedLevelClassifyingIso A B j P PB PD PE).symm⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.IsomorphismRepresentation
