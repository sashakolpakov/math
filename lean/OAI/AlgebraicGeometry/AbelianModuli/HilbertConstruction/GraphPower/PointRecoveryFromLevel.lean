import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PointRecoveryFromEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelIso

/-! # Point Recovery From Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PointRecoveryFromLevel.RationalGlobalGraphPowerLocus

noncomputable section

/-! Pass an original full-level embedding recovery to the rational
graph-power polarization classifier before specializing its parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_point_recovery_of_fullLevel
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
    (k : A.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left P.dimension)
    (hrec : Embedded.LevelIso.EmbeddedFullLevelRecovery A.abelian A.level (F.pullback x.left)
      k (Embedded.LevelIso.abelianProjectiveBaseChangeEmbedding F.abelian P x.left))
    (hn : P.dimension = E.projectivePresentation.dimension)
    (hk : HEq k.left E.projectivePresentation.embedding.left) :
    ∃ z : T ⟶ Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ,
      z ≫ Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.inclusion M F P qS d hd δ hδ = x ∧
      Nonempty (Moduli.Isomorphisms.LevelPreservingIso A
        ((Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.universalFamily M F P qS d hd δ hδ).pullback z.left)) := by
  obtain ⟨e, hgroup, hlevel, hembedding⟩ := hrec
  exact @PointRecoveryFromEmbedding.RationalGlobalGraphPowerLocus.exists_point_recovery_of_embedding R _ _ M _ g N F P qS d hd δ hδ
    T x A E hE e hgroup hlevel hn
    ((heq_of_eq (congrArg Over.Hom.left hembedding)).trans hk)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PointRecoveryFromLevel.RationalGlobalGraphPowerLocus
