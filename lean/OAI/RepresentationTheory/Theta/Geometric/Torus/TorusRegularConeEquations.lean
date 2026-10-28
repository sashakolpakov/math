import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodAlgebraicCoordinates
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPointwiseRegularProjection
import OAI.Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates
import OAI.Geometry.ComplexTorus.RiemannProjectivity.RegularCoordinate

/-! # Torus Regular Cone Equations -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusRegularConeEquations.CM.Algebraization.RegularConeEquations

noncomputable section

open Set _root_.Polynomial
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent OAI.Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates

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
    ∃ (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ))
      (m : ℕ) (e : (Fin (n + 1) → ℂ) ≃L[ℂ]
        ((Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) × (Fin m → ℂ)))
      (F : Fin m → Polynomial (MvPolynomial (Fin (Module.finrank ℂ (Φ.space) + 1)) ℂ)),
      (∀ w, (e w).1 = L w) ∧
      Geometry.ComplexTorus.RiemannProjectivity.BranchCoefficientsAt.Constructions.BranchCoefficients.HasHolomorphicInverseAt
        (Subtype.val : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) → (Fin (n + 1) → ℂ))
        (fun w => L w) v ∧
      (∀ j, F j ≠ 0) ∧
      (∀ j, ((F j).map (MvPolynomial.eval (L v))).derivative.eval (Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate e j v) ≠ 0) ∧
      ∀ j w, w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) →
        (F j).eval₂ (MvPolynomial.eval (L w)) (Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate e j w) = 0 := by
  classical
  obtain ⟨L, hker, hp, hs, hfinite, hInv⟩ :=
    TorusPointwiseRegularProjection.CM.Algebraization.PointwiseRegularProjection.exists_at_parameter Φ f hf hd i z hi v hv
  have hLs : Function.Surjective L := fun y => by
    obtain ⟨w, hw⟩ := hs y
    exact ⟨w, hw⟩
  obtain ⟨m, e, he, hsep⟩ := Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.exists_split L hLs v.val (hfinite (L v))
  have hpoly (j : Fin m) := TorusPeriodAlgebraicCoordinates.CM.Algebraization.PeriodAlgebraicCoordinates.coordinate_equation Φ f hf hd L hker hs
    (Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate e j) (Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate_pair_surjective L e he j)
  choose k F hk hF hgen hroots using hpoly
  have hvi : v.val i = 1 := by rw [hv]; simp [Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization]
  have hv0 : v.val ≠ 0 := by
    intro hzero
    have h := congrFun hzero i
    rw [hvi] at h
    exact one_ne_zero h
  have hLv : L v ≠ 0 := fun h => hv0 (hker v v.property h)
  have hfin : ((fun w : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L w) ⁻¹' {L v}).Finite := by
    apply Set.Finite.of_finite_image (f := (Subtype.val : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) → Fin (n + 1) → ℂ))
      ((hfinite (L v)).subset ?_) Subtype.val_injective.injOn
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  obtain ⟨q, hvq, hq, hdq⟩ := hInv
  refine ⟨L, m, e, F, he, ⟨q, hvq, hq, hdq⟩, ?_, ?_, ?_⟩
  · intro j hj
    exact (hF j 0).1.ne_zero (by rw [hj, Polynomial.map_zero])
  · intro j
    apply Geometry.ComplexTorus.RiemannProjectivity.RegularCoordinate.Constructions.RegularCoordinateDerivative.derivative_ne_zero hp.isClosedMap
      ((Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate e j).continuous.comp continuous_subtype_val) q hq hvq hLv hfin
      (fun w hwL hwl => ?_) (F j) (hF j) (hgen j)
    · intro y t
      constructor
      · rintro ⟨w, hw⟩
        exact (hroots j y t).mp ⟨w, w.property, hw⟩
      · intro ht
        obtain ⟨w, hw, heq⟩ := (hroots j y t).mpr ht
        exact ⟨⟨w, hw⟩, heq⟩
    · apply Subtype.ext
      by_contra hwv
      exact hsep w w.property hwL hwv j hwl
  · intro j w hw
    exact (hroots j (L w) (Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate e j w)).mp ⟨w, hw, rfl⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusRegularConeEquations.CM.Algebraization.RegularConeEquations
