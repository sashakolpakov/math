import OAI.RepresentationTheory.Theta.Geometric.DoubleLatticeCosets
import OAI.RepresentationTheory.Theta.Geometric.Finite.AutomorphyTrace
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF

/-! # Double Lattice Trace -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Sections on the doubled lattice descend by the proved finite trace. -/

open scoped ContDiff

variable (Φ : Torus.Data.CM.ProjectivePeriodData)
  (H : Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ) (J : Φ.AutomorphyFactor)
  (hdouble : ∀ l : Φ.periodIntegerLattice, l ∈ Φ.doubleSubgroup → ∀ z,
    J.value l z = Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy (Φ.halfHermitian H) l.val z)

include hdouble

theorem Torus.Data.CM.ProjectivePeriodData.doubleLatticeTheta_invariant (n : ℕ)
    (t : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection (Φ.halfHermitian H) Φ.doubledLattice.toAddSubgroup n)
    (l : Φ.periodIntegerLattice) (hl : l ∈ Φ.doubleSubgroup) :
    (J.power n).translateSection l t = t := by
  funext z
  change t (z + l.val) / J.value l z ^ n = t z
  have h := t.translates ⟨l.val, (Φ.mem_doubleSubgroup l).mp hl⟩ z
  change t (z + l.val) = Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy (Φ.halfHermitian H) l.val z ^ n * t z at h
  rw [← hdouble l hl z] at h
  rw [h, mul_div_cancel_left₀ _ (pow_ne_zero _ (J.value_ne_zero l z))]

theorem Torus.Data.CM.ProjectivePeriodData.doubleLatticeTheta_trace (hJ : ∀ l, ContDiff ℂ ∞ (J.value l)) (n : ℕ)
    (t : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection (Φ.halfHermitian H) Φ.doubledLattice.toAddSubgroup n)
    (p : Φ.space) (htp : t p ≠ 0)
    (hvanish : ∀ l : Φ.periodIntegerLattice,
      (QuotientAddGroup.mk l : Φ.periodIntegerLattice ⧸ Φ.doubleSubgroup) ≠ 0 → t (p + l.val) = 0) :
    ∃ s : Φ.space → ℂ, ContDiff ℂ ∞ s ∧ s p ≠ 0 ∧
      ∀ (l : Φ.periodIntegerLattice) z, s (z + l.val) = J.value l z ^ n * s z := by
  let ht := Φ.doubleLatticeTheta_invariant H J hdouble n t
  let trace := (J.power n).finiteTrace Φ.doubleSubgroup t ht
  refine ⟨trace, (J.power n).finiteTrace_contDiff (fun l => (hJ l).pow n) Φ.doubleSubgroup t ht
    (contDiffOn_univ.mp
      (Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn
        isOpen_univ t.differentiable.differentiableOn)), ?_,
    (J.power n).finiteTrace_translates Φ.doubleSubgroup t ht⟩
  have heq : trace p = t p := (J.power n).finiteTrace_eq_of_vanish Φ.doubleSubgroup t ht p hvanish
  exact heq ▸ htp

end

end OAI.RepresentationTheory.Theta.Geometric
