import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel
import OAI.AlgebraicGeometry.Resolution.Blowups.JacobianNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TransverseHypersurfaceCoordinates

/-! # Dual Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Recover an exact dual frame for the actual labelled equations of a local boundary model. -/

universe u v

variable {k A : Type u} {ι : Type v} [Field k] [CommRing A] [Algebra k A]
  [Fintype ι] [DecidableEq ι] {w : ι → A}

/-- A unit-scaled normal-crossing model provides exact dual derivations
for all actual equations on a principal neighborhood of any prime where
those equations vanish. The denominator explicitly avoids that prime. -/
theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.exists_local_dual_frame (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k A ι w)
    (q : Ideal A) [q.IsPrime] (hw : ∀ j, w j ∈ q) :
    ∃ f ∉ q, ∃ D : ι → Derivation k (Localization.Away f) (Localization.Away f),
      ∀ i j, D i (algebraMap A (Localization.Away f) (w j)) = if i = j then 1 else 0 := by
  classical
  have hex : ∀ j, ∃ s, M.coordinate j = some s := by
    intro j
    cases h : M.coordinate j with
    | none =>
        have he : w j = M.multiplier j := by rw [M.equation j, h, mul_one]
        have hu : IsUnit (w j) := he ▸ M.multiplierUnit j
        exact False.elim (q.notMem_of_isUnit hu (hw j))
    | some s => exact ⟨s, rfl⟩
  choose s hs using hex
  have hinj : Function.Injective s := by
    intro i j hij
    apply M.distinct i j (s i) (hs i)
    rw [hij]
    exact hs j
  let : Algebra (MvPolynomial M.indices k) A := M.map.toAlgebra
  let : Algebra.Etale (MvPolynomial M.indices k) A := RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower k (MvPolynomial M.indices k) A :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  let z : ι → A := fun j => M.map (MvPolynomial.X (s j))
  let D : ι → Derivation k A A := fun j => Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (s j)
  have hD : ∀ i j, D i (z j) = if i = j then 1 else 0 := by
    intro i j
    change Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (s i)
      (algebraMap (MvPolynomial M.indices k) A (MvPolynomial.X (s j))) = _
    rw [Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X]
    simp only [hinj.eq_iff]
  have he : w = fun j => M.multiplier j * z j := by
    funext j
    simpa only [hs j] using M.equation j
  have hz : ∀ j, z j ∈ q := by
    intro j
    apply (q.unit_mul_mem_iff_mem (M.multiplierUnit j)).mp
    rw [← congrFun he j]
    exact hw j
  have hdet : (JacobianDerivationFrame.Construction.derivationJacobian D w).det ∉ q := by
    rw [he]
    exact JacobianNeighborhood.Construction.unit_boundary_jacobian_not_mem z D hD M.multiplier M.multiplierUnit q hz
  refine ⟨(JacobianDerivationFrame.Construction.derivationJacobian D w).det, hdet,
    JacobianDerivationFrame.Construction.normalizedJacobianFrame (JacobianNeighborhood.Construction.jacobianNeighborhoodDerivation D w)
      (fun j => algebraMap A (JacobianNeighborhood.Construction.derivationJacobianNeighborhood D w) (w j)), ?_⟩
  exact JacobianDerivationFrame.Construction.normalizedJacobianFrame_dual _ _ (JacobianNeighborhood.Construction.jacobianNeighborhood_jacobian_isUnit D w)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
