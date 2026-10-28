import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFinite
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

/-! # Section Finiteness -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.SectionFiniteness

noncomputable section

/-! Actual global sections of a coherent projective module are finite over
the actual ring of functions on the base. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveGlobalSections_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {σ : Type} [Fintype σ] [LinearOrder σ]
    (M : (Proj (MvPolynomial.homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(Spec (CommRingCat.of R), ⊤)
      ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj M) := by
  let π := SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let U := SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)
  have hU : IsOpenCover U :=
    IsOpenCover.mk (SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R))
  have : Module.Finite Γ(Spec (CommRingCat.of R), ⊤)
      ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology 0) :=
    SheafCohomology.Projective.TwistCechFinite.MvPolynomial.finiteType_orderedBaseCechComplex_homology_module_finite M 0
  let := SheafCohomology.Projective.BaseZeroSections.baseGlobalSectionsModule π M
  exact Module.Finite.equiv (SheafCohomology.Projective.BaseZeroSections.orderedBaseCechHZeroGlobalSectionsLinearEquiv π M U hU)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.SectionFiniteness
