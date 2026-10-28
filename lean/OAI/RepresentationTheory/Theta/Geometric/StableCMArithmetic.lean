import OAI.RepresentationTheory.Theta.Geometric.StableCMRealLattice
import OAI.Geometry.ComplexBall.ArithmeticPresentation
import OAI.NumberTheory.ArithmeticGroups.Lattices.Discrete

/-! # Stable CM Arithmetic -/

namespace OAI.RepresentationTheory.Theta.Geometric.StableCMArithmetic

noncomputable section

/-! Discreteness of the exact original lattice stabilizer at the active
complex place, with the compact conjugate factors accounted for. -/

set_option backward.isDefEq.respectTransparency false
open scoped Classical _root_.NumberField
open _root_.NumberField OAI.NumberTheory.ArithmeticGroups.Lattices.Discrete.Construction

open OAI.Geometry.ComplexBall.ArithmeticPresentation.Quotient

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (L : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (b : E)

def stableUnitarySubgroup : Subgroup (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) where
  carrier := {g | ∀ x, Matrix.SpecialLinearGroup.toLin' g.val x ∈ L ↔ x ∈ L}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    simpa only [Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply] using
      (hg (Matrix.SpecialLinearGroup.toLin' h.val x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have h := hg (Matrix.SpecialLinearGroup.toLin' (g⁻¹).val x)
    have he : Matrix.SpecialLinearGroup.toLin' g.val
        (Matrix.SpecialLinearGroup.toLin' (g⁻¹).val x) = x := by
      rw [Subgroup.coe_inv, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    exact (he ▸ h).symm

variable (hL : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice L)
    (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

theorem stableUnitary_map_stabilizer :
    (stableUnitarySubgroup L b).map (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0).toMonoidHom =
      (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).latticeStabilizer (StableCMRealLattice.stableRealLattice L hL δ hδ hδ0) := by
  ext g
  obtain ⟨g, rfl⟩ := (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0).surjective g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  change (∀ x, Matrix.SpecialLinearGroup.toLin' g.val x ∈ L ↔ x ∈ L) ↔
    ∀ y, Matrix.SpecialLinearGroup.toLin' (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0 g).val y ∈
      (StableCMRealLattice.stableRealLattice L hL δ hδ hδ0).module ↔ y ∈ (StableCMRealLattice.stableRealLattice L hL δ hδ hδ0).module
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := (Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0).surjective y
    rw [← Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates_action, StableCMRealLattice.stableRealLattice_mem, StableCMRealLattice.stableRealLattice_mem]
    exact h x
  · intro h x
    have he := h (Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0 x)
    rw [← Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates_action, StableCMRealLattice.stableRealLattice_mem, StableCMRealLattice.stableRealLattice_mem] at he
    exact he

variable (μ : E →+* ℂ)
    (hpos : ∀ ν : E →+* ℂ, ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ → 0 < (ν b).re)

include hL hpos in
theorem stableUnitary_arithmeticPresentation :
    NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.IsArithmeticPresentation (Geometry.ComplexBall.Connected.ArithmeticQuotient.originalConnectedSemisimpleUnitaryGroup b hb hb0 δ hδ hδ0)
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap b μ) (stableUnitarySubgroup L b) := by
  refine ⟨StableCMRealLattice.stableRealLattice L hL δ hδ hδ0, Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0,
    {Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ}, Geometry.ComplexBall.ArithmeticPresentation.Quotient.originalArchimedeanProductEquiv b hb δ hδ hδ0 μ, ?_, ?_, ?_⟩
  · intro v hv
    exact Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.originalUnitary_omittedPlace_compact b hb δ hδ hδ0 μ hpos v hv
  · exact stableUnitary_map_stabilizer L b hL hb δ hδ hδ0
  · exact Geometry.ComplexBall.ArithmeticPresentation.Quotient.originalArchimedeanProductEquiv_diagonal b hb δ hδ hδ0 μ

include hL hb hb0 δ hδ hδ0 hpos in
theorem stableUnitary_archimedean_discrete :
    DiscreteTopology ((stableUnitarySubgroup L b).map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap b μ)) := by
  apply NumberTheory.ArithmeticGroups.Lattices.Discrete.Construction.arithmetic_subgroup_discrete
    (Geometry.ComplexBall.Connected.ArithmeticQuotient.originalConnectedSemisimpleUnitaryGroup b hb hb0 δ hδ hδ0)
    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap b μ) (stableUnitarySubgroup L b) (stableUnitarySubgroup L b)
  · exact stableUnitary_arithmeticPresentation L b hL hb hb0 δ hδ hδ0 μ hpos
  · exact Subgroup.Commensurable.refl _

end

end OAI.RepresentationTheory.Theta.Geometric.StableCMArithmetic
