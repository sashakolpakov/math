import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Matrix Unit Neighborhoods -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixUnitNeighborhoods.CM

noncomputable section

/-! ThetaCycle: the actual topology of a matrix-unit subgroup is detected by
the matrix and its inverse, with neighborhoods translated to zero. -/

open scoped _root_.Topology
open Filter

theorem matrix_unit_subgroup_zero_neighborhood
    {R I : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Fintype I] [DecidableEq I] (G : Subgroup (Matrix I I R)ˣ)
    (U : Set G) (hU : U ∈ 𝓝 (1 : G)) :
    ∃ V : Set (Matrix I I R × Matrix I I R), V ∈ 𝓝 (0, 0) ∧
      ∀ g : G, (g.val.val - 1, (g⁻¹).val.val - 1) ∈ V → g ∈ U := by
  let e : (Matrix I I R × (Matrix I I R)ᵐᵒᵖ) ≃ₜ (Matrix I I R × Matrix I I R) :=
    (Homeomorph.refl _).prodCongr MulOpposite.opHomeomorph.symm
  let c : G → Matrix I I R × Matrix I I R := fun g => e (Units.embedProduct _ g.val)
  have hi : Topology.IsInducing c :=
    e.isInducing.comp (Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal)
  rw [hi.nhds_eq_comap] at hU
  obtain ⟨W, hW, hWU⟩ := mem_comap.mp hU
  let shift : Matrix I I R × Matrix I I R → Matrix I I R × Matrix I I R :=
    fun p => (1 + p.1, 1 + p.2)
  have hs : Continuous shift := (continuous_const.add continuous_fst).prodMk
    (continuous_const.add continuous_snd)
  have hzero : shift (0, 0) = c 1 := by ext i j <;> simp [shift, c, e]
  refine ⟨shift ⁻¹' W, hs.continuousAt.preimage_mem_nhds (hzero.symm ▸ hW), ?_⟩
  intro g hg
  apply hWU
  have he : shift (g.val.val - 1, (g⁻¹).val.val - 1) = c g := by
    change (1 + (g.val.val - 1), 1 + ((g⁻¹).val.val - 1)) = (g.val.val, (g⁻¹).val.val)
    congr 1 <;> abel
  change c g ∈ W
  change shift (g.val.val - 1, (g⁻¹).val.val - 1) ∈ W at hg
  exact he ▸ hg

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixUnitNeighborhoods.CM
