import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex

/-! # Symplectic Action Continuity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticActionContinuity.CM

noncomputable section

/-! Continuity of symplectic actions survives coordinate relabeling and
conjugation by a fixed symplectic matrix. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization

variable {I J X : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [TopologicalSpace X]

theorem reindex (e : I ≃ J) (s : X → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hs : ∀ v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf, Continuous (fun x => (s x).val *ᵥ v))
    (v : (J ⊕ J) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : Continuous (fun x => (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e (s x)).val *ᵥ v) := by
  let r := RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex (e.sumCongr e) (K := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
  have he : (fun x => (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e (s x)).val *ᵥ v) =
      (fun x => r ((s x).val *ᵥ r.symm v)) := by
    funext x
    have h := RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_action e (s x) (r.symm v)
    change (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e (s x)).val *ᵥ r (r.symm v) = _ at h
    rw [Homeomorph.apply_symm_apply] at h
    exact h
  rw [he]
  exact r.continuous.comp (hs (r.symm v))

omit [Fintype J] [DecidableEq J] in
theorem conjugate (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (s : X → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hs : ∀ v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf, Continuous (fun x => (s x).val *ᵥ v))
    (v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : Continuous (fun x => (a⁻¹ * s x * a).val *ᵥ v) := by
  have he : (fun x => (a⁻¹ * s x * a).val *ᵥ v) =
      (fun x => (a⁻¹).val *ᵥ ((s x).val *ᵥ (a.val *ᵥ v))) := by
    funext x
    change ((a⁻¹).val * (s x).val * a.val) *ᵥ v = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [he]
  exact continuous_const.matrix_mulVec (hs (a.val *ᵥ v))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticActionContinuity.CM
