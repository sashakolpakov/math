import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Base Map Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert

noncomputable section

/-! Normalized graph embeddings retain their original family under an
equality of base maps and the canonical composition of two pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R]

def NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.baseCongr
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ} [NeZero N]
    {A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S} {i : Fin (N ^ (2 * g))}
    {f f' : S ⟶ Spec (.of R)}
    (D : NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk f) A i) (h : f = f') :
    NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk f') A i := by
  subst f'
  exact D

def NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.ofPullbackComp
    {S T U : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ} [NeZero N]
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (p : T ⟶ S) (q : U ⟶ T)
    (b : S ⟶ Spec (.of R)) {i : Fin (N ^ (2 * g))}
    (D : NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk (q ≫ (p ≫ b))) ((A.pullback p).pullback q) i) :
    NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk ((q ≫ p) ≫ b)) (A.pullback (q ≫ p)) i :=
  NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.ofLevelIso R _
    (NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.baseCongr R D (Category.assoc q p b).symm)
    (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A p q).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert
