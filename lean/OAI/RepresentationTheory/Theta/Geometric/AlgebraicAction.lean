import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange
import OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints

/-! # Algebraic Action -/

namespace OAI.RepresentationTheory.Theta.Geometric.AlgebraicAction

noncomputable section

/-! Algebraization of an actual holomorphic ring action, with its ring laws
proved by faithfulness on complex points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM
open scoped _root_.CategoryTheory.MonObj _root_.Manifold

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper A.toOver.hom :=
  A.variety.presentation.projective.isProper

abbrev AbelianPoints (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) := Additive (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
abbrev AbelianModel (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :=
  Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ

def algebraicEndPoints (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A.toOver →+* AddMonoid.End (AbelianPoints A) where
  toFun f := (f.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))).hom
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem algebraicEndPoints_injective (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Function.Injective (algebraicEndPoints A) := by
  intro f g h
  apply AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_injective A.toOver
  apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points
  intro p
  have he := DFunLike.congr_fun h (Additive.ofMul p)
  exact (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_points A.toOver f _ p).symm.trans
    ((congrArg Additive.toMul he).trans (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_points A.toOver g _ p))

theorem algebraicEndPoints_preimage (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : AddMonoid.End (AbelianPoints A))
    (hf : MDifferentiable 𝓘(ℂ, AbelianModel A) 𝓘(ℂ, AbelianModel A)
      (fun p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver => (f (Additive.ofMul p)).toMul)) :
    ∃ g : AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A.toOver, algebraicEndPoints A g = f := by
  let fmul : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver →* AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver :=
    { toFun := fun p => (f (Additive.ofMul p)).toMul
      map_one' := f.map_zero
      map_mul' := fun p q => f.map_add (Additive.ofMul p) (Additive.ofMul q) }
  obtain ⟨g, hg, he⟩ := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM.holomorphic_group_hom_is_algebraic A A fmul hf
  let := hg
  refine ⟨AlgebraicGeometry.AbelianScheme.TateComparison.End.endOfSchemeMap A.toOver g, ?_⟩
  apply AddMonoidHom.ext
  intro p
  exact he p.toMul

/-- Every holomorphic integral action lifts to the native algebraic
endomorphism ring; its evaluation is the original action. -/
theorem exists_algebraic_ring_action {R : Type} [Ring R] (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (r : R →+* AddMonoid.End (AbelianPoints A))
    (hr : ∀ a, MDifferentiable 𝓘(ℂ, AbelianModel A) 𝓘(ℂ, AbelianModel A)
      (fun p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver => (r a (Additive.ofMul p)).toMul)) :
    ∃ ralg : R →+* AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A.toOver,
      ∀ a, algebraicEndPoints A (ralg a) = r a := by
  choose g hg using fun a => algebraicEndPoints_preimage A (r a) (hr a)
  let ralg : R →+* AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A.toOver :=
    { toFun := g
      map_zero' := by apply algebraicEndPoints_injective A; rw [hg, map_zero, map_zero]
      map_one' := by apply algebraicEndPoints_injective A; rw [hg, map_one, map_one]
      map_add' := by intro a b; apply algebraicEndPoints_injective A; rw [map_add, hg, hg, hg, map_add]
      map_mul' := by intro a b; apply algebraicEndPoints_injective A; rw [map_mul, hg, hg, hg, map_mul] }
  exact ⟨ralg, hg⟩

/-- Conjugate an additive ring action by its actual group comparison. -/
def transportAdditiveAction {R T U : Type} [Ring R] [AddCommGroup T] [AddCommGroup U]
    (e : T ≃+ U) (r : R →+* AddMonoid.End T) : R →+* AddMonoid.End U where
  toFun a := e.toAddMonoidHom.comp ((r a).comp e.symm.toAddMonoidHom)
  map_zero' := by
    apply AddMonoidHom.ext
    intro p
    change e (r 0 (e.symm p)) = 0
    rw [map_zero]
    exact e.map_zero
  map_one' := by
    apply AddMonoidHom.ext
    intro p
    change e (r 1 (e.symm p)) = p
    rw [map_one]
    exact e.apply_symm_apply p
  map_add' := by
    intro a b
    apply AddMonoidHom.ext
    intro p
    change e (r (a + b) (e.symm p)) = e (r a (e.symm p)) + e (r b (e.symm p))
    rw [map_add]
    exact e.map_add _ _
  map_mul' := by
    intro a b
    apply AddMonoidHom.ext
    intro p
    change e (r (a * b) (e.symm p)) = e (r a (e.symm (e (r b (e.symm p)))))
    rw [map_mul, e.symm_apply_apply]
    rfl

end

end OAI.RepresentationTheory.Theta.Geometric.AlgebraicAction
