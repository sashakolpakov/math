import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineRationalExists
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleDivisor

/-! # Affine Complement -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineComplement.Construction.AffineComplementDivisor

noncomputable section

/-! Affine opens of smooth integral separated schemes are complements of effective line-bundle divisors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_lineBundle {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of K)) [Smooth f] (U : X.affineOpens) [Nonempty U.1] :
    ∃ (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf), AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = U.1 := by
  obtain ⟨T, hT⟩ := AffineRationalExists.Construction.AffineRationalCoordinates.exists_finset f U
  obtain ⟨L, s, hs⟩ := PoleDivisor.Construction.FinitePoleDivisor.exists_lineBundle f T
  refine ⟨L, s, ?_⟩
  apply SetLike.ext
  intro x
  exact (hs x).trans (hT x).symm

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineComplement.Construction.AffineComplementDivisor
