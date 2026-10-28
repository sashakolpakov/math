import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusCone
import OAI.Geometry.ComplexTorus.RiemannProjectivity.GraphRegular
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusRegularConeEquations

/-! # Torus Regular Cone Neighborhood -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusRegularConeNeighborhood.CM.Algebraization.RegularConeNeighborhood

noncomputable section

open Set _root_.Polynomial
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent OAI.Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalizedGraph.Constructions.LocalizedGraphGerms

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {a b : ℕ}

def splitPoint (e : V ≃L[ℂ] ((Fin a → ℂ) × (Fin b → ℂ))) (w : V) :
    Fin a ⊕ Fin b → ℂ := Sum.elim (e w).1 (e w).2

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
    ∃ (m : ℕ) (e : (Fin (n + 1) → ℂ) ≃L[ℂ]
        ((Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) × (Fin m → ℂ)))
      (F : Fin m → Polynomial (MvPolynomial (Fin (Module.finrank ℂ (Φ.space) + 1)) ℂ))
      (s : Geometry.ComplexTorus.RiemannProjectivity.LocalizedGraph.Constructions.LocalizedGraphGerms.smoothRing F) (q : Geometry.ComplexTorus.RiemannProjectivity.LocalizedGraph.Constructions.LocalizedGraphGerms.smoothRing F →ₐ[ℂ] ℂ),
      (∀ w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), ∀ j,
        MvPolynomial.eval (splitPoint e w) (Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation j (F j)) = 0) ∧
      (∀ p, q (Geometry.ComplexTorus.RiemannProjectivity.GraphRegular.Constructions.GraphVanishingIdeal.polynomialMap F p) = MvPolynomial.eval (splitPoint e v.val) p) ∧
      q s ≠ 0 ∧ Algebra.Smooth ℂ
        (Localization.Away (Ideal.Quotient.mk
          (Geometry.ComplexTorus.RiemannProjectivity.GraphRegular.Constructions.GraphVanishingIdeal.vanishingIdeal F (splitPoint e '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))) s)) := by
  obtain ⟨L, m, e, F, he, hInv, hF, hder, hzero⟩ :=
    TorusRegularConeEquations.CM.Algebraization.RegularConeEquations.exists_at_parameter Φ f hf hd i z hi v hv
  obtain ⟨r, hvr, hr, hdr⟩ := hInv
  have hx : L v ∈ r.target := by
    rw [← congrFun hr v]
    exact r.map_source hvr
  have hinv : r.symm (L v) = v := by
    rw [← congrFun hr v]
    exact r.left_inv hvr
  let ψ := fun y => (e (r.symm y).val).2
  have hψ : DifferentiableOn ℂ ψ r.target :=
    (e.differentiable.comp_differentiableOn hdr).snd
  have hbase (y) (hy : y ∈ r.target) : (e (r.symm y).val).1 = y := by
    rw [he, ← congrFun hr (r.symm y)]
    exact r.right_inv hy
  have hz (y) (hy : y ∈ r.target) (j : Fin m) :
      (F j).eval₂ (MvPolynomial.eval y) (ψ y j) = 0 := by
    have h := hzero j (r.symm y).val (r.symm y).property
    rw [← he, hbase y hy, Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate_apply] at h
    exact h
  have hdψ (j : Fin m) : ((F j).map (MvPolynomial.eval (L v))).derivative.eval (ψ (L v) j) ≠ 0 := by
    simpa only [ψ, hinv, Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate_apply] using hder j
  have hS (y) (hy : y ∈ r.target) : Geometry.ComplexTorus.RiemannProjectivity.GraphGermsOn.Constructions.GraphGerms.graph ψ y ∈
      splitPoint e '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := by
    refine ⟨(r.symm y).val, (r.symm y).property, ?_⟩
    funext j
    cases j with
    | inl j => exact congrFun (hbase y hy) j
    | inr j => rfl
  obtain ⟨s, q, hq, hs, hsm⟩ := Geometry.ComplexTorus.RiemannProjectivity.GraphRegular.Constructions.GraphVanishingIdeal.exists_smooth_point_neighborhood
    F hF (L v) ψ r.open_target hx hψ hz hdψ _ hS
  refine ⟨m, e, F, s, q, ?_, ?_, hs, hsm⟩
  · intro w hw j
    change MvPolynomial.eval (Sum.elim (e w).1 (e w).2)
      (Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation j (F j)) = 0
    rw [Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.eval_equation, he]
    exact hzero j w hw
  intro p
  rw [hq]
  have hg : Geometry.ComplexTorus.RiemannProjectivity.GraphGermsOn.Constructions.GraphGerms.graph ψ (L v) = splitPoint e v.val := by
    funext j
    cases j with
    | inl j => exact congrFun (he v.val).symm j
    | inr j => change (e (r.symm (L v)).val).2 j = (e v.val).2 j; rw [hinv]
  rw [hg]

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusRegularConeNeighborhood.CM.Algebraization.RegularConeNeighborhood
