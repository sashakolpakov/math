import OAI.RepresentationTheory.Theta.Geometric.Torus.AbelianModel
import OAI.RepresentationTheory.Theta.Geometric.Torus.Manifold
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicAction

/-! # Hom -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.Hom

noncomputable section

/-! Integral linear maps of the actual period lattices induce algebraic
group maps between their abelian models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable (Φ Ψ : Data.CM.ProjectivePeriodData)
  (f : Φ.space →ₗ[ℂ] Ψ.space)
  (hf : ∀ v, v ∈ Φ.periodIntegerLattice → f v ∈ Ψ.periodIntegerLattice)

def torusLinearMap : Φ.periodTorus →+ Ψ.periodTorus :=
  QuotientAddGroup.map Φ.periodIntegerLattice.toAddSubgroup Ψ.periodIntegerLattice.toAddSubgroup
    f.toAddMonoidHom hf

@[simp] theorem torusLinearMap_mk (v : Φ.space) :
    torusLinearMap Φ Ψ f hf (QuotientAddGroup.mk v) = QuotientAddGroup.mk (f v) := rfl

theorem torusLinearMap_contMDiff :
    ContMDiff 𝓘(ℂ, Φ.space) 𝓘(ℂ, Ψ.space) ∞ (torusLinearMap Φ Ψ f hf) := by
  apply Φ.contMDiff_of_periodProjection
  exact Ψ.periodProjection_contMDiff.comp (LinearMap.toContinuousLinearMap f).contDiff.contMDiff

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem exists_algebraic_torus_map (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (eA : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (eB : Ψ.periodTorus ≃ₘ⟮𝓘(ℂ, Ψ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel B)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
    (hA : ∀ u v, eA (u + v) = eA u * eA v)
    (hB : ∀ u v, eB (u + v) = eB u * eB v) :
    ∃ g : A.toOver ⟶ B.toOver, IsMonHom g ∧
      ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (eA t) = eB (torusLinearMap Φ Ψ f hf t) := by
  let a : Φ.periodTorus ≃+ AlgebraicAction.AbelianPoints A :=
    { toFun := fun t => Additive.ofMul (eA t)
      invFun := fun p => eA.symm p.toMul
      left_inv := eA.symm_apply_apply
      right_inv := eA.apply_symm_apply
      map_add' := hA }
  let b : Ψ.periodTorus ≃+ AlgebraicAction.AbelianPoints B :=
    { toFun := fun t => Additive.ofMul (eB t)
      invFun := fun p => eB.symm p.toMul
      left_inv := eB.symm_apply_apply
      right_inv := eB.apply_symm_apply
      map_add' := hB }
  let F := b.toAddMonoidHom.comp ((torusLinearMap Φ Ψ f hf).comp a.symm.toAddMonoidHom)
  let Fmul : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver →* AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver :=
    { toFun := fun p => (F (Additive.ofMul p)).toMul
      map_one' := F.map_zero
      map_mul' := fun p q => F.map_add (Additive.ofMul p) (Additive.ofMul q) }
  have hF : MDifferentiable 𝓘(ℂ, AlgebraicAction.AbelianModel A) 𝓘(ℂ, AlgebraicAction.AbelianModel B) Fmul := by
    exact (eB.contMDiff.comp ((torusLinearMap_contMDiff Φ Ψ f hf).comp eA.symm.contMDiff)).mdifferentiable
      (by norm_num)
  obtain ⟨g, hg, hpoints⟩ := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM.holomorphic_group_hom_is_algebraic A B Fmul hF
  refine ⟨g, hg, ?_⟩
  intro t
  have h := hpoints (eA t)
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (eA t) =
    eB (torusLinearMap Φ Ψ f hf (eA.symm (eA t))) at h
  simpa only [eA.symm_apply_apply] using h

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.Hom
