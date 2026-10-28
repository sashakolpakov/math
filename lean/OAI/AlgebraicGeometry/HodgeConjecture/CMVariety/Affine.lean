import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicCone
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicRegularConeNeighborhood
import OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint

/-! # Affine -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Affine.CM.Abelian.Algebraization.AffineConeSmoothPoint

noncomputable section

open Set _root_.Polynomial
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicRegularConeNeighborhood.CM.Abelian.Algebraization.RegularConeNeighborhood

variable {n : ℕ}

theorem exists_at_parameter (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (i : Fin (n + 1)) (z : Φ.space)
    (hi : f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (v : ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
    (hv : v.val = Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, 1)) :
    ∃ (m : ℕ) (e : (Fin (n + 1) → ℂ) ≃L[ℂ]
        ((Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) × (Fin m → ℂ)))
      (q : (MvPolynomial (Fin (Module.finrank ℂ (Φ.space) + 1) ⊕ Fin m) ℂ ⧸
        MvPolynomial.vanishingIdeal ℂ (AlgebraicRegularConeNeighborhood.CM.Abelian.Algebraization.RegularConeNeighborhood.splitPoint e '' ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))) →ₐ[ℂ] ℂ),
      (∀ p, q (Ideal.Quotient.mk _ p) = MvPolynomial.eval (AlgebraicRegularConeNeighborhood.CM.Abelian.Algebraization.RegularConeNeighborhood.splitPoint e v.val) p) ∧
      Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime q ∈ Algebra.smoothLocus ℂ
        (MvPolynomial (Fin (Module.finrank ℂ (Φ.space) + 1) ⊕ Fin m) ℂ ⧸
          MvPolynomial.vanishingIdeal ℂ (AlgebraicRegularConeNeighborhood.CM.Abelian.Algebraization.RegularConeNeighborhood.splitPoint e '' ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))) := by
  obtain ⟨m, e, F, s, q, hrel, hq, hs, hsm⟩ :=
    AlgebraicRegularConeNeighborhood.CM.Abelian.Algebraization.RegularConeNeighborhood.exists_at_parameter Φ f hf hd i z hi v hv
  let J := Ideal.span (range (fun j => Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation j (F j)))
  let I := MvPolynomial.vanishingIdeal ℂ (AlgebraicRegularConeNeighborhood.CM.Abelian.Algebraization.RegularConeNeighborhood.splitPoint e '' ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
  have hJI : J ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩ _ ⟨w, hw, rfl⟩
    exact hrel w hw j
  have hk : I.map (Geometry.ComplexTorus.RiemannProjectivity.GraphRegular.Constructions.GraphVanishingIdeal.polynomialMap F) ≤ RingHom.ker q.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change q (Geometry.ComplexTorus.RiemannProjectivity.GraphRegular.Constructions.GraphVanishingIdeal.polynomialMap F p) = 0
    rw [hq]
    exact hp (AlgebraicRegularConeNeighborhood.CM.Abelian.Algebraization.RegularConeNeighborhood.splitPoint e v.val) ⟨v.val, v.property, rfl⟩
  obtain ⟨qI, hqI, hpoint⟩ := Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.ReferenceQuotientSmoothPoint.exists_smooth_point
    J I hJI (Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SmoothEquationPoint.presentation F).jacobian q hk s hs hsm
  refine ⟨m, e, qI, ?_, hpoint⟩
  intro p
  exact (hqI p).trans (hq p)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Affine.CM.Abelian.Algebraization.AffineConeSmoothPoint
