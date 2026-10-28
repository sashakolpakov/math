import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdentityParameterIdealRecovery
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FamilyIdealVanishing

/-! # Ideal Vanishing Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IdealVanishingLocus

noncomputable section

/-! An ideal on a proper flat family over a locally noetherian base has an actual closed vanishing locus, with its exact condition on all over-scheme tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem proper_over_ideal_vanishing_closed_locus
    {S : Scheme.{u}} [IsLocallyNoetherian S] (X : Over S) [IsProper X.hom] [Flat X.hom]
    (I : X.left.IdealSheafData) :
    ∃ (Z : Over S) (j : Z ⟶ Over.mk (𝟙 S)), IsClosedImmersion j.left ∧
      ∀ T : Over S, I.comap (IdentityParameterIdealRecovery.overProductSourceMap X T) = ⊥ ↔
        ∃! y : T ⟶ Z, y ≫ j = Over.mkIdTerminal.from T := by
  have : IsLocallyNoetherian (Over.mk (𝟙 S)).left := inferInstanceAs (IsLocallyNoetherian S)
  obtain ⟨Z, j, hj, htest, _⟩ := HilbertScheme.Presentations.Proper.FamilyIdealVanishing.Core.proper_family_ideal_vanishing_closed_locus X
    (B := Over.mk (𝟙 S)) (I.comap (IdentityParameterIdealRecovery.overProductSourceMap X (Over.mk (𝟙 S))))
  refine ⟨Z, j, hj, fun T => ?_⟩
  have h := htest T (Over.mkIdTerminal.from T)
  rw [IdentityParameterIdealRecovery.identityParameter_ideal_recovery] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IdealVanishingLocus
