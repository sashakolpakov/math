import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction

/-! # Complex Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions

noncomputable section

/-! The actual projective diagonal and its restrictions, with the
native complex manifold structures used by supported Thom theory. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance : IsIntegral V.toOver.left := V.property
local instance : Smooth V.toOver.hom := V.presentation.smooth
local instance : IsIntegral (Ambient.Constructions.productVariety V V).toOver.left := (Ambient.Constructions.productVariety V V).property
local instance : Smooth (Ambient.Constructions.productVariety V V).toOver.hom := (Ambient.Constructions.productVariety V V).presentation.smooth

theorem diagonal_native_dimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom + V.complexDimension =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Ambient.Constructions.productVariety V V).toOver.hom := by
  change V.complexDimension + V.complexDimension = (Ambient.Constructions.productVariety V V).complexDimension
  exact (Ambient.Constructions.product_dimension V V).symm

abbrev diagonalImmersion : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Scheme.ClosedImmersion.Constructions.schemeManifold (Ambient.Constructions.productVariety V V).toOver) V.complexDimension :=
  Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (Ambient.Constructions.diagonal V) V.complexDimension (diagonal_native_dimension V)

abbrev diagonalOpenImmersion (U : Opens (Ambient.Constructions.productVariety V V).analyticSpace) :=
  Closed.ImmersionOpenRestriction.Constructions.restrict (diagonalImmersion V) U

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions
