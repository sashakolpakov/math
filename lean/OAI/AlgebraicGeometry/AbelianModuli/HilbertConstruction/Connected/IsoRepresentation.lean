import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ProjectivePolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ZeroGraphUniversalBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ProductPowerEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.LevelIsoFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineIsoRepresentation

/-! # Iso Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.IsoRepresentation

noncomputable section

/-! The full polarized isomorphism functor over a connected Noetherian affine base is represented by a constructed quasi-projective scheme. The embedding and universal graph bound are derived from the polarization. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem connectedNoetherianAffine_polarizedIso_quasiProjective_representation
    {S : Scheme.{u}} [IsAffine S] [IsNoetherian S] [ConnectedSpace S]
    {g N : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i) :
    ∃ M : Over S, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation M) ∧
      Nonempty (Family.LevelIsoFunctor.familyLevelIsoFunctor A B ≅ yoneda.obj M) := by
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let E := Polarized.ProductPowerEmbedding.polarizedProductPowerEmbedding A B
  let j := E.relativeMorphism A.graphBundle B.graphBundle
  obtain ⟨Q, hQ⟩ := ProjectivePolynomial.graph_exists_connectedNoetherianHilbertPolynomial j
    (1 : A.abelian.scheme ⟶ B.abelian.scheme)
  let P := Q.comp (Polynomial.C (2 : ℚ) * Polynomial.X)
  exact ⟨Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P,
    ⟨Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterQuasiProjectivePresentation A B j P⟩,
    ⟨(Family.LevelIsoFunctor.boundedFamilyLevelIsoForgetIso A B j P
      (Polarized.ZeroGraphUniversalBound.polarized_universalGraphBound_of_zeroGraph A B E Q hQ)).symm ≪≫
      (Noetherian.AffineIsoRepresentation.noetherianAffine_boundedPolarizedLevelClassifyingIso A B j P hδ).symm⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.IsoRepresentation
