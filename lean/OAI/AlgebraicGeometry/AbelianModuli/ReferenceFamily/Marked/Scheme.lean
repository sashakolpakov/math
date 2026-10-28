import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicPolarization
import OAI.RepresentationTheory.Theta.Geometric.AbelianScheme
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData

/-! # Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.Scheme

noncomputable section

/-! A marking by 2g integral periods determines the native algebraic
dimension. This packages the same variety and group law as an abelian
scheme of dimension g, and retains its actual endomorphism action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable {g : ℕ} (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (c : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Picard.ThetaConstruction.DefinitionsIntegral.Index g) B)

local instance : IsIntegral B.toOver.left := B.variety.property

include c in
theorem markedVariety_dimension : Betti.AffineDimension.Realization.functionFieldDifferentialDimension B.toOver.hom = g := by
  have h := Picard.ThetaConstruction.IntrinsicPolarization.Geometric.native_tangent_finrank B c
  change Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension B.toOver.hom) → ℂ) = g at h
  simpa only [Module.finrank_fin_fun] using h

def markedAbelianScheme : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase where
  scheme := B.toOver
  group := B.group
  commutative := B.commutative
  proper := (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety B).proper
  smoothDimension := by
    rw [← markedVariety_dimension B c]
    exact (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety B).smoothDimension
  connected := (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety B).connected

def markedAbelianIntegralAction {R : Type*} [CommRing R]
    (σ : ActionData.IntegralAction R (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety B)) : ActionData.IntegralAction R (markedAbelianScheme B c) where
  map := σ.map
  preservesGroup := σ.preservesGroup
  map_zero := σ.map_zero
  map_one := σ.map_one
  map_add := σ.map_add
  map_mul := σ.map_mul

def originalNativeIntegralMarking (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom) :
    ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Picard.ThetaConstruction.DefinitionsIntegral.Index g) (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) :=
  (Intrinsic.Torsion.IntrinsicTorsion.periodBasis (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).reindex
    (finCongr (congrArg (fun n : ℕ => 2 * n) (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq A)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.Scheme
