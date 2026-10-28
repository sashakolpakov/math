import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IdealVanishingLocus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.IdealPullbackComparison

/-! # Ideal Cartesian Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IdealCartesianLocus

noncomputable section

/-! The ideal of a proper flat family vanishes after exactly the base changes factoring through an actual closed parameter locus. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem proper_ideal_baseChange_closed_locus
    {S : Scheme.{u}} [IsLocallyNoetherian S] (X : Over S) [IsProper X.hom] [Flat X.hom]
    (I : X.left.IdealSheafData) :
    ∃ (Z : Over S) (j : Z ⟶ Over.mk (𝟙 S)), IsClosedImmersion j.left ∧
      ∀ T : Over S, I.comap (pullback.fst X.hom T.hom) = ⊥ ↔
        ∃! y : T ⟶ Z, y ≫ j = Over.mkIdTerminal.from T := by
  obtain ⟨Z, j, hj, htest⟩ := IdealVanishingLocus.proper_over_ideal_vanishing_closed_locus X I
  exact ⟨Z, j, hj, fun T => (Product.IdealPullbackComparison.overProduct_ideal_zero_iff_pullback X T I).symm.trans (htest T)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IdealCartesianLocus
