import OAI.AlgebraicGeometry.Comparison.Betti.Affine.PointDerivationRealization
import OAI.AlgebraicGeometry.Comparison.Betti.PointDerivationDescent
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.TangentDerivation
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartCotangentRealization

/-! # Closed Normal Covectors -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ClosedNormalCovectors

noncomputable section

section

/-! Vectors annihilating the original defining ideal are exactly tangents to a smooth affine closed immersion. -/

variable {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
  [IsDomain B] [Algebra.Smooth ℂ B] {m : ℕ}

theorem affineClosedTangent_exists_preimage
    (h : A →ₐ[ℂ] B) (hh : Function.Surjective h)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)
      (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B))
    (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source) (hfx : x.comp h ∈ f.source)
    (v : Fin m → ℂ)
    (hv : ∀ a, h a = 0 → ChartCotangentRealization.affineChartRegularDifferential f (x.comp h) a v = 0) :
    ∃ w : Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ,
      fderiv ℂ (fun z => f ((e.symm z).comp h)) (e x) w = v := by
  let : Algebra A ℂ := (x.comp h).toRingHom.toAlgebra
  let : Algebra B ℂ := x.toRingHom.toAlgebra
  let D : Derivation ℂ A ℂ := TangentDerivation.affineChartTangentDerivation f hf (x.comp h) hfx v
  have hD : ∀ a, h a = 0 → D a = 0 := hv
  obtain ⟨D', hD'⟩ := PointDerivationDescent.pointDerivation_descends h hh x D hD
  obtain ⟨w, hw⟩ := PointDerivationRealization.affinePointDerivation_exists_chartVector e he x hx D'
  refine ⟨w, sub_eq_zero.mp ?_⟩
  apply Cycles.Functoriality.EtaleDifferential.Construction.affineRegularChart_tangent_eq_zero f hf (x.comp h) hfx
  intro a
  change ChartCotangentRealization.affineChartRegularDifferential f (x.comp h) a
    (fderiv ℂ (fun z => f ((e.symm z).comp h)) (e x) w - v) = 0
  rw [map_sub, ← ChartCotangentRealization.affineChartRegularDifferential_comap h e f he hf x hx hfx a w,
    hw, hD']
  change ChartCotangentRealization.affineChartRegularDifferential f (x.comp h) a v -
    ChartCotangentRealization.affineChartRegularDifferential f (x.comp h) a v = 0
  exact sub_self _

end

/-! The original algebraic kernel generates all analytic normal covectors of a smooth affine closed immersion. -/

variable {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
  [IsDomain B] [Algebra.Smooth ℂ B] {m : ℕ}

theorem affineClosedNormalCovectors_span
    (h : A →ₐ[ℂ] B) (hh : Function.Surjective h)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)
      (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B))
    (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source) (hfx : x.comp h ∈ f.source) :
    Submodule.span ℂ (Set.range (fun a : RingHom.ker h.toRingHom =>
      ChartCotangentRealization.affineChartRegularDifferential f (x.comp h) a)) =
        (LinearMap.range
          (fderiv ℂ (fun z => f ((e.symm z).comp h)) (e x)).toLinearMap).dualAnnihilator := by
  let W := Submodule.span ℂ (Set.range (fun a : RingHom.ker h.toRingHom =>
    ChartCotangentRealization.affineChartRegularDifferential f (x.comp h) a))
  let L := (fderiv ℂ (fun z => f ((e.symm z).comp h)) (e x)).toLinearMap
  have hW : W.dualCoannihilator = LinearMap.range L := by
    ext v
    change v ∈ ((Submodule.span ℂ (Set.range (fun a : RingHom.ker h.toRingHom =>
      ChartCotangentRealization.affineChartRegularDifferential f (x.comp h) a))).dualCoannihilator : Set (Fin m → ℂ)) ↔ _
    rw [Submodule.coe_dualCoannihilator_span]
    constructor
    · intro hv
      apply affineClosedTangent_exists_preimage h hh e f he hf x hx hfx v
      intro a ha
      exact hv _ ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨w, rfl⟩ _ ⟨a, rfl⟩
      change ChartCotangentRealization.affineChartRegularDifferential f (x.comp h) a
        (fderiv ℂ (fun z => f ((e.symm z).comp h)) (e x) w) = 0
      rw [← ChartCotangentRealization.affineChartRegularDifferential_comap h e f he hf x hx hfx a w]
      have ha : h a = 0 := a.property
      rw [ha]
      simp [ChartCotangentRealization.affineChartRegularDifferential]
  change W = (LinearMap.range L).dualAnnihilator
  rw [← hW, Subspace.dualCoannihilator_dualAnnihilator_eq]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ClosedNormalCovectors
