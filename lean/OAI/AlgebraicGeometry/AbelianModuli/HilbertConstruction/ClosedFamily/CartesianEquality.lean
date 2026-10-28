import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.EmbeddingCartesianKernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Transport

/-! # Cartesian Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Cartesian recovery of the prescribed embeddings is equality of the actual ideal-defined flat families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Closed.Families.FlatClosedFamily.eq_pullbackAlong_of_isPullback
    {S T : Scheme.{u}} {P : Over S} {Q : Over T}
    (F : Closed.Families.FlatClosedFamily Q) (G : Closed.Families.FlatClosedFamily P)
    (p : Q.left ⟶ P.left) (f : T ⟶ S) (hp : IsPullback p Q.hom P.hom f)
    (q : F.scheme.left ⟶ G.scheme.left) (hq : IsPullback q F.inclusion.left G.inclusion.left p) :
    F = G.pullbackAlong p f hp := by
  have hF : F.inclusion.left.ker = F.ideal := F.ideal.ker_subschemeι
  have hG : G.inclusion.left.ker = G.ideal := G.ideal.ker_subschemeι
  have h := Closed.EmbeddingCartesianKernels.closedEmbedding_ker_of_isPullback F.inclusion.left G.inclusion.left q p hq.flip
  apply Closed.Families.FlatClosedFamily.ext
  exact hF.symm.trans (h.trans (congrArg (fun I => I.comap p) hG))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
