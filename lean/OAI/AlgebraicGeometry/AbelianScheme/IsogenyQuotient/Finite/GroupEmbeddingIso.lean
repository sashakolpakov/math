import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.GroupRankIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Rank

/-! # Group Embedding Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.GroupEmbeddingIso.Construction

noncomputable section

/-! A monomorphism between actually isomorphic finite group schemes
is an isomorphism. Equality of ranks is derived from the given scheme isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
theorem finiteGroup_mono_isIso_of_nonempty_iso
    {k : Type u} [Field k] (G H : Grp (Over (Spec (.of k))))
    [IsCommMonObj G.X] [IsCommMonObj H.X]
    [IsFinite G.X.hom] [Flat G.X.hom] [IsFinite H.X.hom] [Flat H.X.hom]
    (f : G ⟶ H) [Mono f.hom.hom] (e : Nonempty (G ≅ H)) (s : Spec (.of k)) : IsIso f := by
  obtain ⟨e⟩ := e
  let j : G.X ≅ H.X := (Grp.forget _).mapIso e
  exact GroupRankIso.Construction.finiteGroup_mono_isIso_of_finrank_eq G H f s
    (CartierDuality.Rank.Construction.Schemes.overIso_finrank j s)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.GroupEmbeddingIso.Construction
