import OAI.AlgebraicGeometry.CycleClass.Thom.EtaleCoordinateAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange

/-! # Etale Section Vector -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EtaleSectionVector.Constructions

noncomputable section

/-! The actual section vector of etale polynomial coordinates is a
local analytic coordinate map on the native complex-point manifold. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleCoordinateAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleCoordinateDimension.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] (n : ℕ)
  [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

def coordinateSections (i : Fin n) : Γ(X.left, ⊤) :=
  algebraMap (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤) (MvPolynomial.X i)

def coordinateAlgHom : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, ⊤) :=
  IsScalarTower.toAlgHom ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)

theorem coordinateVector_eq_globalCoordinates :
    (Section.VectorHeadChange.Constructions.sectionVectorEquation X n (coordinateSections X n) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → (Fin n → ℂ)) =
      Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates (coordinateAlgHom X n) := by
  funext x i
  exact (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv_eval X x (coordinateSections X n i)).symm

variable [IsIntegral X.left] [Smooth X.hom]

local notation "MX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

theorem coordinateVector_analytic : ContMDiff 𝓘(ℂ, MX) 𝓘(ℂ, Fin n → ℂ) ω
    (Section.VectorHeadChange.Constructions.sectionVectorEquation X n (coordinateSections X n)) := by
  rw [coordinateVector_eq_globalCoordinates]
  exact Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic (coordinateAlgHom X n)

variable [Algebra.FormallyEtale (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

theorem coordinateVector_differential_bijective (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Function.Bijective (mfderiv 𝓘(ℂ, MX) 𝓘(ℂ, Fin n → ℂ)
      (Section.VectorHeadChange.Constructions.sectionVectorEquation X n (coordinateSections X n)) x) := by
  rw [coordinateVector_eq_globalCoordinates]
  exact EtaleCoordinateAnalytic.Constructions.globalCoordinates_unramified_bijective X n (coordinateAlgHom X n)
    (RingHom.formallyUnramified_algebraMap.mpr inferInstance)
    (EtaleCoordinateDimension.Constructions.affine_coordinate_dimension X n) x

theorem coordinateVector_localDiffeomorph : IsLocalDiffeomorph 𝓘(ℂ, MX) 𝓘(ℂ, Fin n → ℂ) ω
    (Section.VectorHeadChange.Constructions.sectionVectorEquation X n (coordinateSections X n)) :=
  fun x => AnalyticLocalInverseAt.Constructions.ProperImage.Construction.isLocalDiffeomorphAt_of_bijective_mfderiv _ (coordinateVector_analytic X n) x
    (coordinateVector_differential_bijective X n x)

theorem exists_coordinate_injective_neighborhood (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ∃ U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X), x ∈ U ∧
      Set.InjOn (Section.VectorHeadChange.Constructions.sectionVectorEquation X n (coordinateSections X n)) U := by
  obtain ⟨q, hx, hq⟩ := coordinateVector_localDiffeomorph X n x
  refine ⟨⟨q.source, q.open_source⟩, hx, ?_⟩
  intro a ha b hb hab
  apply q.injOn ha hb
  exact (hq ha).symm.trans (hab.trans (hq hb))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EtaleSectionVector.Constructions
