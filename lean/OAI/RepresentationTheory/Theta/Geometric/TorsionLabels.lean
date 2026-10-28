import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence

/-! # Torsion Labels -/

namespace OAI.RepresentationTheory.Theta.Geometric.TorsionLabels

noncomputable section

/-! Explicit lattice division points for the native ordered torsion
equivalence. The labels are the original integral coordinates modulo N. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  [Fintype I] (b : Module.Basis I ℤ L)

def latticeCoordinateEquiv : (V ⧸ L.toAddSubgroup) ≃+ (I → UnitAddCircle) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (congrArg Submodule.toAddSubgroup (b.ofZLatticeBasis_span ℝ L))).symm.trans
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion.basisTorusEquiv (b.ofZLatticeBasis ℝ L))

@[simp] theorem latticeCoordinateEquiv_mk (v : V) :
    latticeCoordinateEquiv L b (QuotientAddGroup.mk v) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion.coordinateMap (b.ofZLatticeBasis ℝ L) v := rfl

theorem latticeTorsionEquiv_reference (N : ℕ) [NeZero N] (v : L) :
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion.latticeTorsionEquiv L b N (fun i => (b.repr v i : ZMod N))).val =
      (QuotientAddGroup.mk ((N : ℝ)⁻¹ • v.val) : V ⧸ L.toAddSubgroup) := by
  apply (latticeCoordinateEquiv L b).injective
  change latticeCoordinateEquiv L b
    ((latticeCoordinateEquiv L b).symm (fun i => ZMod.toAddCircle (b.repr v i : ZMod N))) = _
  rw [AddEquiv.apply_symm_apply, latticeCoordinateEquiv_mk]
  funext i
  rw [ZMod.toAddCircle_intCast]
  change (((b.repr v i : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle) =
    ((b.ofZLatticeBasis ℝ L).repr ((N : ℝ)⁻¹ • v.val) i : UnitAddCircle)
  rw [map_smul, Finsupp.smul_apply, b.ofZLatticeBasis_repr_apply ℝ]
  congr 1
  exact div_eq_inv_mul _ _

end

end OAI.RepresentationTheory.Theta.Geometric.TorsionLabels
