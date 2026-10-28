import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EmbeddingUniversalSections

/-! # Arbitrary Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Base change of an actual power embedding retains its degree,
dimension, and projective presentation. Universal completeness gives a
complete basis on every affine test, with no Noetherian condition on it. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S T : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom) (f : T ⟶ S)

def PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingBaseChange :
    Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (A.pullback f).graphBundle (A.pullback f).abelian.scheme.hom :=
  E.baseChangeWithLineIso f (A.pullback f).graphBundle (A.graphBundle_baseChangeIso f)

def PolarizationData.PolarizedAbelianWithFullLevel.completeGraphPowerEmbeddingBaseChange [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsAffine T]
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) (D : E.CompleteSectionData) :
    (A.graphPowerEmbeddingBaseChange E f).CompleteSectionData :=
  E.completeBaseChangeData f (A.pullback f).graphBundle (A.graphBundle_baseChangeIso f)
    (A.completeGraphEmbedding_universalSections hN hunit E D)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
