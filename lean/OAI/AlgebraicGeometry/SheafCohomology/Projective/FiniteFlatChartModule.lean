import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineChartPullback
import Mathlib.Algebra.Module.FinitePresentation

/-! # Finite Flat Chart Module -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteFlatChartModule.Dimension

noncomputable section

/-! Actual inverse-image affine coordinate rings are finite flat modules of the scheme map's rank. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction

universe u

@[instance_reducible]
def affinePreimageSectionAlgebra {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra

theorem affinePreimageSectionScalarTower {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (π : Y ⟶ S) (U : Y.Opens) :
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra π U
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ π) (f ⁻¹ᵁ U)
    letI := affinePreimageSectionAlgebra f U
    IsScalarTower Γ(S, ⊤) Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra π U
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ π) (f ⁻¹ᵁ U)
  let := affinePreimageSectionAlgebra f U
  apply IsScalarTower.of_algebraMap_eq'
  exact (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenScalarMap_pullback f π U).symm

theorem affinePreimageSectionModule_finite {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := affinePreimageSectionAlgebra f U
    Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  let := affinePreimageSectionAlgebra f U
  exact (RingHom.finite_algebraMap).mp (f.finite_app U hU)

theorem affinePreimageSectionModule_flat {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] [Flat f] (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := affinePreimageSectionAlgebra f U
    Module.Flat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  let := affinePreimageSectionAlgebra f U
  apply (RingHom.flat_algebraMap_iff).mp
  change (f.app U).hom.Flat
  simpa only [Scheme.Hom.appLE_eq_app] using f.flat_appLE hU (hU.preimage f) le_rfl

theorem affinePreimageSectionModule_finitePresentation {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (U : Y.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(Y, U)] :
    letI := affinePreimageSectionAlgebra f U
    Module.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  let := affinePreimageSectionAlgebra f U
  have := affinePreimageSectionModule_finite f U hU
  exact Module.finitePresentation_of_finite _ _

theorem affinePreimageSectionModule_rank {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [Flat f] (U : Y.Opens) (hU : IsAffineOpen U)
    (t : PrimeSpectrum Γ(Y, U)) :
    letI := affinePreimageSectionAlgebra f U
    Module.rankAtStalk (R := Γ(Y, U)) Γ(X, f ⁻¹ᵁ U) t = f.finrank (hU.fromSpec t) := by
  let := affinePreimageSectionAlgebra f U
  have := affinePreimageSectionModule_finite f U hU
  have := affinePreimageSectionModule_flat f U hU
  exact (Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U) t).symm.trans
    (AffineChartPullback.Dimension.finrank_affine_preimage f U hU t)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteFlatChartModule.Dimension
