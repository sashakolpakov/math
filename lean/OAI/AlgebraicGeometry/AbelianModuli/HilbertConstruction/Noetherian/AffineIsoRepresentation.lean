import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.DualProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.IsomorphismRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.UniversalLevelRigidity

/-! # Affine Iso Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineIsoRepresentation

noncomputable section

/-! The bounded complete moduli-isomorphism functor of polarized objects over a Noetherian affine base is represented by the constructed quasi-projective parameter. All required projective presentations are supplied by the objects' polarization. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
universe u

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherian S]
variable {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
variable [IsClosedImmersion j.left] (P : Polynomial ℚ)

def noetherianAffine_boundedPolarizedLevelClassifyingIso (hδ : ∀ i, 0 < δ i) :
    yoneda.obj (Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P) ≅ BoundedModuli.IsomorphismFunctor.boundedFamilyLevelIsoFunctor A B j P := by
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  exact BoundedModuli.IsomorphismRepresentation.boundedPolarizedLevelClassifyingIso A B j P B.projectivePresentation_of_noetherian_affine
    (A.dualProjectivePresentation_of_noetherian_affine hδ)
    (B.dualProjectivePresentation_of_noetherian_affine hδ)

theorem noetherianAffine_boundedPolarizedLevelIso_quasiProjective_representation
    (hδ : ∀ i, 0 < δ i) :
    ∃ M : Over S, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation M) ∧
      Nonempty (BoundedModuli.IsomorphismFunctor.boundedFamilyLevelIsoFunctor A B j P ≅ yoneda.obj M) :=
  ⟨Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P,
    ⟨Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterQuasiProjectivePresentation A B j P⟩,
    ⟨(noetherianAffine_boundedPolarizedLevelClassifyingIso A B j P hδ).symm⟩⟩

theorem noetherianAffine_boundedPolarizedLevelIso_points_subsingleton
    (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (T : Over S) :
    Subsingleton (T ⟶ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P) := by
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  have := UniversalLevelRigidity.polarizedPullbackIsomorphisms_subsingleton_of_noetherian_affine A B hN T
  let e := (noetherianAffine_boundedPolarizedLevelClassifyingIso A B j P hδ).app (.op T)
  refine ⟨fun f q => ?_⟩
  apply (CategoryTheory.injective_of_mono e.hom)
  exact Subtype.ext (Subsingleton.elim _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineIsoRepresentation
