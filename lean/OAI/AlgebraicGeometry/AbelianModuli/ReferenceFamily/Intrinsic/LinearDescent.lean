import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps

/-! # Linear Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LinearDescent.IntrinsicLinearMaps

noncomputable section

/-! Every complex linear map preserving the actual period lattices
descends to a holomorphic group map and then to an actual algebraic map.
The algebraization uses the proved HolomorphicAlgebraicity theorem on the native atlases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Manifold _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : ChartedSpace (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (Maps.IntrinsicAlgebraicMaps.torus A).Point :=
  HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.quotient_chartedSpace (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (L : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (hL : Geometry.ComplexTorus.BettiLattice.CM.Construction.PreservesLattice (A := Maps.IntrinsicAlgebraicMaps.torus A) (B := Maps.IntrinsicAlgebraicMaps.torus B) L)

def nativeLinearPointMap : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver →* ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver where
  toFun x := (Maps.IntrinsicAlgebraicMaps.periodAddEquiv B (Geometry.ComplexTorus.BettiLattice.CM.Construction.descend (A := Maps.IntrinsicAlgebraicMaps.torus A) (B := Maps.IntrinsicAlgebraicMaps.torus B) L hL ((Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).symm (Additive.ofMul x)))).toMul
  map_one' := by
    change (Maps.IntrinsicAlgebraicMaps.periodAddEquiv B (Geometry.ComplexTorus.BettiLattice.CM.Construction.descend (A := Maps.IntrinsicAlgebraicMaps.torus A) (B := Maps.IntrinsicAlgebraicMaps.torus B) L hL ((Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).symm 0))).toMul = 1
    rw [map_zero, map_zero, map_zero]
    rfl
  map_mul' x y := by
    change (Maps.IntrinsicAlgebraicMaps.periodAddEquiv B (Geometry.ComplexTorus.BettiLattice.CM.Construction.descend (A := Maps.IntrinsicAlgebraicMaps.torus A) (B := Maps.IntrinsicAlgebraicMaps.torus B) L hL ((Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).symm (Additive.ofMul x + Additive.ofMul y)))).toMul = _
    rw [map_add, map_add, map_add]
    rfl

theorem nativeLinearPointMap_holomorphic :
    MDifferentiable (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)) (fun x => nativeLinearPointMap L hL x) := by
  have hd : MDifferentiable (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)) (Geometry.ComplexTorus.BettiLattice.CM.Construction.descend (A := Maps.IntrinsicAlgebraicMaps.torus A) (B := Maps.IntrinsicAlgebraicMaps.torus B) L hL) :=
    HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.mdifferentiable_of_local_lifts (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B)
      (Geometry.ComplexTorus.BettiLattice.CM.Construction.descend (A := Maps.IntrinsicAlgebraicMaps.torus A) (B := Maps.IntrinsicAlgebraicMaps.torus B) L hL) (Geometry.ComplexTorus.BettiLattice.CM.Construction.descend_holomorphic (A := Maps.IntrinsicAlgebraicMaps.torus A) (B := Maps.IntrinsicAlgebraicMaps.torus B) L hL)
  exact (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph_mdifferentiable Maps.IntrinsicAlgebraicMaps.algebraization B).comp
    (hd.comp (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph_symm_mdifferentiable Maps.IntrinsicAlgebraicMaps.algebraization A))

theorem nativeLinearPointMap_period (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    nativeLinearPointMap L hL (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Maps.IntrinsicAlgebraicMaps.algebraization A ((Maps.IntrinsicAlgebraicMaps.torus A).proj v)) =
      HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Maps.IntrinsicAlgebraicMaps.algebraization B ((Maps.IntrinsicAlgebraicMaps.torus B).proj (L v)) := by
  change (Maps.IntrinsicAlgebraicMaps.periodAddEquiv B (Geometry.ComplexTorus.BettiLattice.CM.Construction.descend (A := Maps.IntrinsicAlgebraicMaps.torus A) (B := Maps.IntrinsicAlgebraicMaps.torus B) L hL ((Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).symm (Maps.IntrinsicAlgebraicMaps.periodAddEquiv A ((Maps.IntrinsicAlgebraicMaps.torus A).proj v))))).toMul = _
  rw [(Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).symm_apply_apply]
  exact congrArg (fun w : (Maps.IntrinsicAlgebraicMaps.torus B).Point => (Maps.IntrinsicAlgebraicMaps.periodAddEquiv B w).toMul)
    (Geometry.ComplexTorus.BettiLattice.CM.Construction.descend_lifts (A := Maps.IntrinsicAlgebraicMaps.torus A) (B := Maps.IntrinsicAlgebraicMaps.torus B) L hL v)

theorem exists_nativeLinear_algebraic_map :
    ∃ g : A.toOver ⟶ B.toOver, IsMonHom g ∧
      ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = nativeLinearPointMap L hL x :=
  Maps.IntrinsicAlgebraicMaps.algebraization A B (nativeLinearPointMap L hL) (nativeLinearPointMap_holomorphic L hL)

def nativeLinearDescend : A.toOver ⟶ B.toOver :=
  (exists_nativeLinear_algebraic_map L hL).choose

instance nativeLinearDescend_isMonHom : IsMonHom (nativeLinearDescend L hL) :=
  (exists_nativeLinear_algebraic_map L hL).choose_spec.1

theorem nativeLinearDescend_points (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (nativeLinearDescend L hL) x = nativeLinearPointMap L hL x :=
  (exists_nativeLinear_algebraic_map L hL).choose_spec.2 x

theorem nativeLinearDescend_period (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (nativeLinearDescend L hL)
      (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Maps.IntrinsicAlgebraicMaps.algebraization A ((Maps.IntrinsicAlgebraicMaps.torus A).proj v)) =
        HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Maps.IntrinsicAlgebraicMaps.algebraization B ((Maps.IntrinsicAlgebraicMaps.torus B).proj (L v)) :=
  (nativeLinearDescend_points L hL _).trans (nativeLinearPointMap_period L hL v)

theorem linearLift_nativeLinearDescend : Maps.IntrinsicLinearMaps.linearLift (nativeLinearDescend L hL) = L := by
  symm
  apply Maps.IntrinsicLinearMaps.linearLift_unique (nativeLinearDescend L hL) L hL
  intro v
  apply (Maps.IntrinsicAlgebraicMaps.periodAddEquiv B).injective
  have he := (Maps.IntrinsicAlgebraicMaps.periodAddEquiv B).apply_symm_apply
    (Additive.ofMul (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (nativeLinearDescend L hL)
      (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Maps.IntrinsicAlgebraicMaps.algebraization A ((Maps.IntrinsicAlgebraicMaps.torus A).proj v))))
  exact he.trans (congrArg Additive.ofMul (nativeLinearDescend_period L hL v))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LinearDescent.IntrinsicLinearMaps
