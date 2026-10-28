import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Instances.Matrix

/-! # Integral Open -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralOpen.Intrinsic

noncomputable section

/-! The actual integral special-linear subgroup is open in its matrix topology. -/

open scoped Classical _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates.TestTransport

variable (q : ℕ) [Fact q.Prime]

theorem integralSL3_isOpen : IsOpen (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q : Set (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q)) := by
  have hunit : IsOpen {x : Padic q | ‖x‖ ≤ 1} := by
    have he : Set.range (fun x : PadicInt q => (x : Padic q)) = {x : Padic q | ‖x‖ ≤ 1} := by
      ext x
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    rw [← he]
    exact PadicInt.isOpenEmbedding_coe.isOpen_range
  have he : (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q : Set (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q)) =
      {g | ∀ i j, ‖g.val i j‖ ≤ 1} := Set.ext (IntegralCoordinates.TestTransport.integralSL3_iff_entries q)
  rw [he]
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  have hc : Continuous (fun g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q => g.val i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp
      (continuous_subtype_val : Continuous (fun g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q => g.val)))
  exact hunit.preimage hc

def integralSL3Open : OpenSubgroup (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) where
  toSubgroup := RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q
  isOpen' := integralSL3_isOpen q

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralOpen.Intrinsic
