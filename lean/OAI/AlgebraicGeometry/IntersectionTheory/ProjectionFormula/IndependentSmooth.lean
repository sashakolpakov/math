import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousLocalizationAutomorphism
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.SmoothOfCharts
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport

/-! # Independent Smooth -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IndependentSmooth

noncomputable section

/-! Every independent tuple of linear forms defines a smooth
ambient projective projection away from its center. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis.GradedMap

theorem away_of_map_eq {m n : ℕ} (r : ℕ)
    (f g : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (he : f = g) (s : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m)
    (h : RingHom.IsStandardSmoothOfRelativeDimension r (Away.map g s)) :
    RingHom.IsStandardSmoothOfRelativeDimension r (Away.map f s) := by
  subst g
  exact h

theorem away {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hL : LinearIndependent ℂ L) (i : Fin (m + 1)) :
    RingHom.IsStandardSmoothOfRelativeDimension (n - m)
      (Away.map (Projective.ConeSupport.coordinates L) (MvPolynomial.X i)) := by
  obtain ⟨h, e, _, he⟩ := Projection.CoordinateNormalForm.exists_equiv L hL
  let j := Fin.castLE (Nat.add_le_add_right h 1)
  let f := Projection.CoordinateNormalForm.standard h
  have hs : RingHom.IsStandardSmoothOfRelativeDimension (n - m) (Away.map f (MvPolynomial.X i)) :=
    StandardSmooth.Projection.away j (Fin.castLE_injective _) i
  have hc := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.left
    (Away.map f (MvPolynomial.X i))
    (HomogeneousLocalizationAutomorphism.equivalence e (f (MvPolynomial.X i))) hs
  have hg : RingHom.IsStandardSmoothOfRelativeDimension (n - m)
      (Away.map ((LinearFormBasis.GradedMap.gradedHom e.toLinearMap).comp f) (MvPolynomial.X i)) := by
    rw [Away.map_comp]
    exact hc
  exact away_of_map_eq (n - m) (Projective.ConeSupport.coordinates L)
    ((LinearFormBasis.GradedMap.gradedHom e.toLinearMap).comp f) he (MvPolynomial.X i) hg

theorem smooth {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hL : LinearIndependent ℂ L) : SmoothOfRelativeDimension (n - m)
      (Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)) :=
  Projection.SmoothOfCharts.smooth (n - m) (Projective.ConeSupport.coordinates L) (away L hL)

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IndependentSmooth
