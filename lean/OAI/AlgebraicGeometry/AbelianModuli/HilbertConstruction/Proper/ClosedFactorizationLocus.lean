import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IdealCartesianLocus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.FactorizationBaseChangeIdeal

/-! # Closed Factorization Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ClosedFactorizationLocus

noncomputable section

/-! Factorization of a map from a proper flat family through a fixed closed immersion is represented by an actual closed base locus, on all tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem proper_closed_factorization_locus
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X P Z : Over S}
    [IsProper X.hom] [Flat X.hom] (j : Z ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P) :
    ∃ (B : Over S) (k : B ⟶ Over.mk (𝟙 S)), IsClosedImmersion k.left ∧
      ∀ T : Over S,
        (∃! h : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj Z,
          h ≫ (Over.pullback T.hom).map j = (Over.pullback T.hom).map i) ↔
            ∃! y : T ⟶ B, y ≫ k = Over.mkIdTerminal.from T := by
  obtain ⟨B, k, hk, htest⟩ := IdealCartesianLocus.proper_ideal_baseChange_closed_locus X (j.left.ker.comap i.left)
  exact ⟨B, k, hk, fun T => (Closed.FactorizationBaseChangeIdeal.closedFactorization_baseChange_iff_ideal_zero j i T.hom).symm.trans (htest T)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ClosedFactorizationLocus
