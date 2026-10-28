import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.PointJets
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedRegularJet

/-! # Form Stalk Comparison -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FormStalkComparison

noncomputable section

section

/-! The linear-form maps used to choose projections agree with
the actual homogeneous fractions in the projective stalk. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

theorem chart_form (n : ℕ) (i : Fin (n + 1)) (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    Projective.CoordinateAlgebra.ringEquiv n i (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i a.val) =
      Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
        (Away.mk (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) 1 a.val a.property) := by
  change Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
    (Foundations.Scheme.PolynomialToProjectiveChart.polynomialToProjectiveChart n i (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i a.val)) = _
  rw [Foundations.Scheme.PolynomialToProjectiveChart.polynomialToProjectiveChart_dehomogenize n i 1 a.val a.property]

theorem form {X : Scheme} (n : ℕ) (i : Fin (n + 1)) (j : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (x : X) (hx : j x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    letI := Stalk.PointAlgebra.scalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) x
    HomogeneousFormJets.form n i (Projective.PointJets.coordinateGerm n i j x hx) a =
      j.stalkMap x (Projective.PointJets.StalkFractions.fraction n (j x) a
        ⟨MvPolynomial.X i, Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i⟩ hx) := by
  let := Stalk.PointAlgebra.scalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) x
  let U := Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i
  change X.presheaf.germ (j ⁻¹ᵁ U) x hx
    (j.app U (Projective.CoordinateAlgebra.ringEquiv n i (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i a.val))) = _
  rw [chart_form, ← Projective.PointJets.StalkFractions.germ]
  exact congrArg (fun f : Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, U) ⟶ X.presheaf.stalk x => f
    (Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
      (Away.mk (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) 1 a.val a.property)))
    (Scheme.Hom.germ_stalkMap j U x hx).symm

end

/-! The value of a normalized linear form vanishes precisely on its
projective zero locus. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

namespace ProjectiveFractionUnits

theorem fraction (n : ℕ) (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (a s : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (hs : s.val ∉ x.asHomogeneousIdeal) :
    IsUnit (Projective.PointJets.StalkFractions.fraction n x a s hs) ↔
      a.val ∉ x.asHomogeneousIdeal := by
  refine (MulEquiv.isUnit_map (Proj.stalkIso' (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) x).symm).trans ?_
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk']
  exact IsLocalization.AtPrime.isUnit_mk'_iff _ _ _ _

theorem evaluation {K R : Type} [Field K] [CommRing R] [Algebra K R]
    [IsLocalRing R] (ε : R →ₐ[K] K) (r : R) : ε r = 0 ↔ ¬ IsUnit r := by
  change r ∈ AugmentedCotangent.ideal ε ↔ _
  rw [AugmentedRegularJet.ideal_eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem form {X : Scheme} (n : ℕ) (i : Fin (n + 1)) (j : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (hp : p ≫ (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) = 𝟙 _)
    (hx : j (p (IsLocalRing.closedPoint ℂ)) ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    letI := Stalk.PointAlgebra.scalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
      (p (IsLocalRing.closedPoint ℂ))
    Stalk.PointAlgebra.evaluation (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) p hp
      (HomogeneousFormJets.form n i
        (Projective.PointJets.coordinateGerm n i j (p (IsLocalRing.closedPoint ℂ)) hx) a) = 0 ↔
      a.val ∈ (j (p (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal := by
  let := Stalk.PointAlgebra.scalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
    (p (IsLocalRing.closedPoint ℂ))
  rw [evaluation, FormStalkComparison.form,
    isUnit_map_iff (j.stalkMap (p (IsLocalRing.closedPoint ℂ))).hom, fraction, not_not]

end ProjectiveFractionUnits

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FormStalkComparison
