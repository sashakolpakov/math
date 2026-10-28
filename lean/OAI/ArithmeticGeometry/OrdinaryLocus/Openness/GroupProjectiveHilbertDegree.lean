import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveHilbertDimension
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateBundleIso
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenGroupChartDimension

/-! # Group Projective Hilbert Degree -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupProjectiveHilbertDegree.Construction

noncomputable section

/-! The Hilbert polynomial of a projective embedding of the geometric group has its full dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem group_projective_Hilbert_natDegree
    {K R : Type u} [Field K] [IsAlgClosed K] [CommRing R] [IsNoetherianRing R]
    {σ : Type} [Fintype σ] [LinearOrder σ]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (hfield : IsField Γ(Spec (.of R), ⊤))
    (f : A.left ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (j : σ) (P : Polynomial ℚ) (b : ℕ)
    (hP : ∀ n : ℕ, b ≤ n →
      (Module.finrank Γ(Spec (.of R), ⊤)
        ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
          ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) : ℚ) =
        P.eval (n : ℚ)) :
    (P.natDegree : WithBot ℕ∞) = topologicalKrullDim A.left := by
  let := hfield.toField
  have : IsIntegral A.left := ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group A
  let x : A.left := Classical.choice inferInstance
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show f x ∈ ⨆ i : σ, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i by
      rw [AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]; trivial)
  have : Nonempty (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i) := ⟨⟨x, hi⟩⟩
  have hd := ProjectiveHilbertDimension.Construction.closedProjective_Hilbert_natDegree hfield f i P b (fun n hn => by
    let e := (Scheme.Modules.pullback f).mapIso (ProjectiveCoordinateBundleIso.Construction.projectiveTwistCoordinateIso (R := R) j i n)
    have he := ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).mapIso e).toLinearEquiv.finrank_eq
    exact (congrArg (fun d : ℕ => (d : ℚ)) he).symm.trans (hP n hn))
  exact hd.trans (OpenGroupChartDimension.Construction.group_affine_chart_krullDimension A _
    ((AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) i).preimage f))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupProjectiveHilbertDegree.Construction
