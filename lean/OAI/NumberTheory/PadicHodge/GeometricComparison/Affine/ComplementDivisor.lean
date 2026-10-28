import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.PoleDivisor
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineRationalExists
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleDivisor

/-! # Complement Divisor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.ComplementDivisor.AffineComplementDivisor

noncomputable section

/-! Affine complements on smooth geometrically integral schemes over arbitrary fields. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_lineBundle {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of K)) [Smooth f] [GeometricallyIntegral f] (U : X.affineOpens) [Nonempty U.1] :
    ∃ (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf), AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = U.1 := by
  obtain ⟨T, hT⟩ := AlgebraicGeometry.Quotients.FiniteDescent.AffineRationalExists.Construction.AffineRationalCoordinates.exists_finset f U
  obtain ⟨L, s, hs⟩ := Finite.PoleDivisor.FinitePoleDivisor.exists_lineBundle f T
  refine ⟨L, s, ?_⟩
  apply SetLike.ext
  intro x
  exact (hs x).trans (hT x).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.ComplementDivisor.AffineComplementDivisor
