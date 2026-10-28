import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusFiniteConeFibers
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodCoordinateEquations
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusConePolynomialEquations
import OAI.Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation
import OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusConeSurjectivity

/-! # Torus Period Algebraic Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodAlgebraicCoordinates.CM.Algebraization.PeriodAlgebraicCoordinates

noncomputable section

open Set _root_.Polynomial

variable {n : ℕ}

theorem coordinate_equation (Φ : Data.CM.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ))
    (hker : ∀ v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L v = 0 → v = 0)
    (hsurj : Function.Surjective (fun v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v))
    (l : (Fin (n + 1) → ℂ) →L[ℂ] ℂ) (hl : Function.Surjective (L.prod l)) :
    ∃ (k : ℕ) (F : Polynomial (MvPolynomial (Fin (Module.finrank ℂ (Φ.space) + 1)) ℂ)),
      0 < k ∧ (∀ y, (F.map (MvPolynomial.eval y)).Monic ∧
        (F.map (MvPolynomial.eval y)).natDegree = k) ∧
      Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation.Constructions.GlobalMonicEquation.GenericallySeparable F ∧ ∀ x z, (x, z) ∈ (fun v => (L v, l v)) '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ↔
        F.eval₂ (MvPolynomial.eval x) z = 0 := by
  let T := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)
  let S := (fun v => (L v, l v)) '' T
  have hT : IsClosed T := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone (range f) hf.isClosed_range
  have hTc := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone (range f)
  have hTa := TorusFiniteConeFibers.CM.Algebraization.FiniteConeFibers.cone_holomorphic_of_period_embedding Φ f hf hd
  have hLp := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hT hTc L hker
  have hLf := TorusFiniteConeFibers.CM.Algebraization.FiniteConeFibers.finite_proper_cone_fiber L hLp hker hTa
  have hpairker : ∀ v ∈ T, (L.prod l) v = 0 → v = 0 :=
    fun v hv hzero => hker v hv (congrArg Prod.fst hzero)
  have hp := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hT hTc (L.prod l) hpairker
  have hS : IsClosed S := by
    have h := hp.isClosedMap.isClosed_range
    convert! h using 1
    ext u
    exact ⟨fun ⟨v, hv, he⟩ => ⟨⟨v, hv⟩, he⟩,
      fun ⟨v, he⟩ => ⟨v, v.property, he⟩⟩
  have hSc : ∀ (a : ℂ) ⦃p⦄, p ∈ S → a • p ∈ S := by
    rintro a p ⟨v, hv, rfl⟩
    exact ⟨a • v, hTc a hv, by simp only [map_smul]; rfl⟩
  have hSker : ∀ p ∈ S, p.1 = 0 → p = 0 := by
    rintro p ⟨v, hv, rfl⟩ hzero
    change (L v, l v) = 0
    rw [hker v hv hzero]
    simp only [map_zero, Prod.zero_eq_mk]
  have hSproper := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hS hSc
    (ContinuousLinearMap.fst ℂ (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) ℂ) hSker
  have hSfinite (x : Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) :
      {z : ℂ | (x, z) ∈ S}.Finite := by
    apply ((hLf x).image l).subset
    rintro z ⟨v, hv, heq⟩
    exact ⟨v, ⟨hv, congrArg Prod.fst heq⟩, congrArg Prod.snd heq⟩
  have hSloc (x : Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) (hx : x ≠ 0)
      (z : ℂ) (hz : (x, z) ∈ S) : TorusPeriodCoordinateEquations.CM.Algebraization.PeriodCoordinateEquations.HasLocalMonicEquation S x z := by
    have ha := Geometry.ComplexTorus.RiemannProjectivity.AnalyticCone.Constructions.AnalyticConeImage.linear_projection (L.prod l) hl hT hTc hpairker hTa
      (x, z) hz (fun hzero => hx (congrArg Prod.fst hzero))
    exact TorusConePolynomialEquations.CM.Algebraization.ConePolynomialEquations.local_equation_of_coordinate_image Φ f hf.isEmbedding
      (fun z i hi => (hd z i hi).1) L hLf l hS hx ha
  obtain ⟨C, _, hbound⟩ := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.norm_le_projection hS hSc
    (ContinuousLinearMap.fst ℂ (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) ℂ) hSker
  have hroot (x : Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) (_ : x ≠ 0)
      (z : ℂ) (hz : (x, z) ∈ S) : ‖z‖ ≤ C * ‖x‖ :=
    (norm_snd_le (x, z)).trans (hbound (x, z) hz)
  have hvertex : ∀ z, ((0 : Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ), z) ∈ S ↔ z = 0 := by
    intro z
    constructor
    · intro hz
      exact congrArg Prod.snd (hSker (0, z) hz rfl)
    · intro hz
      subst z
      exact ⟨0, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.zero_mem_projectiveCone _, by simp only [map_zero]⟩
  have hne : ∃ (x : Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ),
      x ≠ 0 ∧ ∃ z, (x, z) ∈ S := by
    obtain ⟨v, hv⟩ := hsurj (fun _ => 1)
    refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0), l v, v, v.property, ?_⟩
    exact Prod.ext hv rfl
  exact Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation.Constructions.VertexEquation.exists_exact_equation hSproper hSfinite hSloc hroot hvertex hne

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodAlgebraicCoordinates.CM.Algebraization.PeriodAlgebraicCoordinates
