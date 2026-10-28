import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusFiniteConeFibers
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusRegularCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusConeInverse
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusConeSurjectivity

/-! # Torus Pointwise Regular Projection -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPointwiseRegularProjection.CM.Algebraization.PointwiseRegularProjection

noncomputable section

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent

variable {n : ℕ}

theorem exists_at_parameter (Φ : Data.CM.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (i : Fin (n + 1)) (z : Φ.space)
    (hi : f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
    (hv : v.val = Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, 1)) :
    ∃ L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ),
      (∀ w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L w = 0 → w = 0) ∧
      IsProperMap (fun w : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L w) ∧
      Function.Surjective (fun w : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L w) ∧
      (∀ y, {w : Fin (n + 1) → ℂ | w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ∧ L w = y}.Finite) ∧
      Geometry.ComplexTorus.RiemannProjectivity.BranchCoefficientsAt.Constructions.BranchCoefficients.HasHolomorphicInverseAt
        (Subtype.val : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) → (Fin (n + 1) → ℂ)) (fun w => L w) v := by
  let r : Φ.space → Fin n → ℂ := fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))
  let T := Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.tangentMap i r z
  have hT : Function.Injective T := Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.tangentMap_injective i (hd z i hi).2
  let e₀ : (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) ≃L[ℂ] (Φ.space × ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨L, hker, hreg⟩ := TorusRegularCone.CM.Algebraization.RegularCone.regular_projection_of_period_embedding Φ f hf.continuous
    (fun z i hi => (hd z i hi).1) (T.comp e₀.toContinuousLinearMap) (hT.comp e₀.injective)
  have hLT : Function.Bijective (L.comp T) :=
    (Function.Bijective.of_comp_iff (L.comp T) e₀.bijective).mp hreg
  have hder : HasFDerivAt (fun p => L (Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i r p)) (L.comp T) (z, 1) :=
    L.hasFDerivAt.comp (z, 1) (Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.hasFDerivAt_parameterization i (hd z i hi).1)
  have hInv := TorusConeInverse.CM.Algebraization.ConeInverse.holomorphic_inverse_of_regular_period_parameter Φ f hf.isEmbedding
    (fun z i hi => (hd z i hi).1) L i z 1 one_ne_zero hi v hv
    (by rw [hder.fderiv]; exact hLT)
  have hclosed := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone (range f) hf.isClosed_range
  have hlocal := TorusFiniteConeFibers.CM.Algebraization.FiniteConeFibers.cone_holomorphic_of_period_embedding Φ f hf hd
  have hp := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hclosed (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _) L hker
  have hinterior : (interior (L '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))).Nonempty := by
    obtain ⟨e, hve, he, _⟩ := hInv
    have hsub : e.target ⊆ L '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := by
      intro y hy
      refine ⟨e.symm y, (e.symm y).property, ?_⟩
      change (fun w : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L w) (e.symm y) = y
      rw [← he]
      exact e.right_inv hy
    exact ⟨e v, interior_mono hsub ((e.open_target.interior_eq).symm ▸ e.map_source hve)⟩
  exact ⟨L, hker, hp, TorusConeSurjectivity.CM.Algebraization.ConeSurjectivity.surjective_cone_projection L hclosed
    (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _) hker hlocal hinterior,
    TorusFiniteConeFibers.CM.Algebraization.FiniteConeFibers.finite_proper_cone_fiber L hp hker hlocal, hInv⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPointwiseRegularProjection.CM.Algebraization.PointwiseRegularProjection
