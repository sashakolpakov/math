import OAI.RepresentationTheory.Theta.Geometric.ProductLattice
import OAI.RepresentationTheory.Theta.Geometric.Torus.Data
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

/-! # Product Period Data -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The product of two projective period tori is a projective period
torus with the literal product lattice. -/

variable (Φ Ψ : Torus.Data.CM.ProjectivePeriodData)

def Torus.Data.CM.ProjectivePeriodData.productHermitian (H : Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ)
    (K : Ψ.space →ₗ⋆[ℂ] Ψ.space →ₗ[ℂ] ℂ) :
    (Φ.space × Ψ.space) →ₗ⋆[ℂ] (Φ.space × Ψ.space) →ₗ[ℂ] ℂ :=
  (H.comp (LinearMap.fst ℂ Φ.space Ψ.space)).compl₂ (LinearMap.fst ℂ Φ.space Ψ.space) +
    (K.comp (LinearMap.snd ℂ Φ.space Ψ.space)).compl₂ (LinearMap.snd ℂ Φ.space Ψ.space)

theorem Torus.Data.CM.ProjectivePeriodData.product_projective : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus (Φ.space × Ψ.space)
    (Φ.periodIntegerLattice.prod Ψ.periodIntegerLattice).toAddSubgroup := by
  let : DiscreteTopology Φ.periodIntegerLattice.toAddSubgroup := Φ.periodIntegerLattice_discrete
  let : DiscreteTopology Ψ.periodIntegerLattice.toAddSubgroup := Ψ.periodIntegerLattice_discrete
  let : DiscreteTopology (Φ.periodIntegerLattice.prod Ψ.periodIntegerLattice).toAddSubgroup :=
    ProductLattice.productLattice_discrete _ _
  let : CompactSpace ((Φ.space × Ψ.space) ⧸
      (Φ.periodIntegerLattice.prod Ψ.periodIntegerLattice).toAddSubgroup) :=
    ProductLattice.productLattice_compact _ _
  obtain ⟨H, hH, hHp, hHi⟩ := (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion Φ.space
    Φ.periodIntegerLattice.toAddSubgroup).mp Φ.projective
  obtain ⟨K, hK, hKp, hKi⟩ := (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion Ψ.space
    Ψ.periodIntegerLattice.toAddSubgroup).mp Ψ.projective
  apply (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion (Φ.space × Ψ.space)
    (Φ.periodIntegerLattice.prod Ψ.periodIntegerLattice).toAddSubgroup).mpr
  refine ⟨Φ.productHermitian Ψ H K, ?_, ?_, ?_⟩
  · intro u v
    change H v.1 u.1 + K v.2 u.2 = star (H u.1 v.1 + K u.2 v.2)
    rw [hH, hK, star_add]
  · intro u hu
    change 0 < (H u.1 u.1 + K u.2 u.2).re
    rw [Complex.add_re]
    by_cases hleft : u.1 = 0
    · have hright : u.2 ≠ 0 := by
        intro hright
        exact hu (Prod.ext hleft hright)
      simpa only [hleft, map_zero, LinearMap.zero_apply, Complex.zero_re, zero_add] using hKp u.2 hright
    · have hright : 0 ≤ (K u.2 u.2).re := by
        by_cases hz : u.2 = 0
        · simp only [hz, map_zero, Complex.zero_re, le_refl]
        · exact (hKp u.2 hz).le
      exact add_pos_of_pos_of_nonneg (hHp u.1 hleft) hright
  · intro u hu v hv
    obtain ⟨m, hm⟩ := hHi u.1 hu.1 v.1 hv.1
    obtain ⟨n, hn⟩ := hKi u.2 hu.2 v.2 hv.2
    refine ⟨m + n, ?_⟩
    change (H u.1 v.1 + K u.2 v.2).im = _
    rw [Complex.add_im, hm, hn, Int.cast_add]

def Torus.Data.CM.ProjectivePeriodData.product : Torus.Data.CM.ProjectivePeriodData where
  space := Φ.space × Ψ.space
  periodIntegerLattice := Φ.periodIntegerLattice.prod Ψ.periodIntegerLattice
  periodIntegerLattice_discrete := ProductLattice.productLattice_discrete _ _
  periodIntegerLattice_full := ProductLattice.productLattice_full _ _
  projective := Φ.product_projective Ψ

end

end OAI.RepresentationTheory.Theta.Geometric
