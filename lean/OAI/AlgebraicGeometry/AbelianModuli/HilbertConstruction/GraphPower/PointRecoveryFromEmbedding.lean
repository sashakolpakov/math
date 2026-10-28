import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GlobalGraphPowerParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PowerEmbeddingCoverage

/-! # Point Recovery From Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PointRecoveryFromEmbedding.RationalGlobalGraphPowerLocus

noncomputable section

/-! A recovered full-level embedding supplies the power line bundle
needed by the original rational polarization classifier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_point_recovery_of_embedding
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (M : Over (Spec (.of R))) [IsNoetherian M.left] {g N : ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N M.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (qS : M.left ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
    (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)
    {T : Over (Spec (.of R))} (x : T ⟶ M)
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
    (hE : E.degree = d)
    (e : A.abelian.scheme ≅ (F.abelian.pullback x.left).scheme) [IsMonHom e.hom]
    (hl : A.level.transport e = F.level.pullback x.left)
    (hn : P.dimension = E.projectivePresentation.dimension)
    (he : HEq (e.hom.left ≫ (P.baseChange x.left).embedding.left)
      E.projectivePresentation.embedding.left) :
    ∃ z : T ⟶ Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ,
      z ≫ Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.inclusion M F P qS d hd δ hδ = x ∧
      Nonempty (Moduli.Isomorphisms.LevelPreservingIso A
        ((Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.universalFamily M F P qS d hd δ hδ).pullback z.left)) := by
  let powerIso := P.baseChangeSectionRecovery E.projectivePresentation E.power E.sectionData
    x.left e hn he ≪≫ E.canonicalDegreeIso d hE
  exact Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.exists_point_recovery M F P qS d hd δ hδ x A e hl powerIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PointRecoveryFromEmbedding.RationalGlobalGraphPowerLocus
