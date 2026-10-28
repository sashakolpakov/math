import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankSchemeImmersion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts

/-! # Rank Quasi Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual glued polynomial rank locus has a projective
compactification over a Noetherian coefficient ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

def Projective.ProjectivePresentations.QuasiProjectivePresentation.ofQuasiCompactImmersion
    {S : Scheme.{u}} [IsNoetherian S] {X Y : Over S}
    (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation X) (j : Y ⟶ X)
    [IsImmersion j.left] [QuasiCompact j.left] : Projective.ProjectivePresentations.QuasiProjectivePresentation Y := by
  have : IsNoetherian X.left := Q.noetherian
  have : NoetherianSpace X.left := IsNoetherian.noetherianSpace
  have : QuasiCompact Q.embedding.left := inferInstance
  have : IsImmersion (j ≫ Q.embedding).left :=
    inferInstanceAs (IsImmersion (j.left ≫ Q.embedding.left))
  have : QuasiCompact (j ≫ Q.embedding).left :=
    inferInstanceAs (QuasiCompact (j.left ≫ Q.embedding.left))
  exact Q.projective.quasiProjectiveImmersion (j ≫ Q.embedding)

theorem Stable.RankQuasiProjectivity.stablePolynomialRankOver_quasiProjective
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {n m : ℕ} (i : Fin m) (D q : ℕ) :
    Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation (Stable.PolynomialRankScheme.stablePolynomialRankOver R (n := n) i D q)) := by
  obtain ⟨Q⟩ := Stable.BalancedProjectiveOpen.stableBalancedQuotientScheme_quasiProjective R i (Nat.succ_pos n)
  exact ⟨Q.ofQuasiCompactImmersion (Stable.PolynomialRankScheme.stablePolynomialRankParameterOver R i D q)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
