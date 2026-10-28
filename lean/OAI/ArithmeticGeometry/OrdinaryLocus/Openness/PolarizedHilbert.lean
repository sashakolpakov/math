import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ClosedProjectiveHilbert
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveTwistComparison

/-! # Polarized Hilbert -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PolarizedHilbert.Construction

noncomputable section

/-! Hilbert polynomials in the actual tensor powers of a projective coordinate bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {r : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateBundle_sections_eventuallyPolynomial
    {X : Scheme.{u}} (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R))
    [IsClosedImmersion f] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : Fin (r + 1)) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (e : (Scheme.Modules.pullback f).obj (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).sheaf ≅
      L.sheaf) (hfield : IsField Γ(Spec (.of R), ⊤)) :
    AlgebraicGeometry.SheafCohomology.Projective.BoundedEventualPolynomial.EventuallyPolynomialOfDegree (fun n =>
      (Module.finrank Γ(Spec (.of R), ⊤)
        ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ
          (R := R) (σ := Fin (r + 1)))).obj
            (SheafTensor.Construction.sheafTensor M (L.tensorPower n).sheaf)) : ℚ)) r := by
  obtain ⟨P, hd, b, hb⟩ := ClosedProjectiveHilbert.Construction.closedProjective_sections_eventuallyPolynomial f M j hfield
  refine ⟨P, hd, b, fun n hn => ?_⟩
  let eT := AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso M
      ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)) ≪≫
    SheafTensor.Construction.sheafTensorCongr (Iso.refl M) (ProjectiveTwistComparison.Construction.pullbackProjectiveTwistIso f j L e n)
  let eG := (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ
    (R := R) (σ := Fin (r + 1)))).mapIso eT
  exact (congrArg (fun k : ℕ => (k : ℚ)) eG.toLinearEquiv.finrank_eq).symm.trans (hb n hn)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PolarizedHilbert.Construction
