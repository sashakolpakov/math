import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedKernelDetection
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricKernelChoices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberPolarizationType
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberLattices

/-! # Chosen Branch Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Chosen projected Tate lattices distinguish actual IsogenyQuotient cover
branches over a geometric source point. Their finite-level kernels
are recovered by surjective Tate evaluation and the original IsogenyQuotient
classification of independently chosen kernel subgroups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  {k : Type} [Field k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} (x : D.GeometricPoint b)
  (frame : D.FiberFrame b x) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (t : Local.IntegralType s)

def Data.SphericalPELAlbaneseData.c46ChosenBranchLattices (c : (D.correspondence t).Fiber x)
    (v : Fin s) : Submodule ℤ_[q] (Fin 3 → ℚ_[q]) :=
  Rational.framedTateLattice frame
    (D.c46FiberIsogeny hIsogenyQuotient t x (c.val ≫ (D.correspondence t).target)
      c.val c.property rfl).isogeny.hom (v, false)

variable (hg : D.IsGoodCompletelySplitPrime) (hgeometry : D.HasIntegralModelGeometry)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q
    D.localCharacter frame)

include hg hgeometry hf in
theorem Data.SphericalPELAlbaneseData.c46ChosenBranchLattices_injective : Function.Injective (D.c46ChosenBranchLattices x frame hIsogenyQuotient t) := by
  intro c d h
  have := FiberLattices.charZero_of_field_spec_map b
  apply (D.c46FiberTorsionSubgroupEquiv t hg b hIsogenyQuotient x).injective
  funext v
  apply Subtype.ext
  ext z
  rw [D.c46FiberTorsionSubgroupEquiv_membership, D.c46FiberTorsionSubgroupEquiv_membership]
  obtain ⟨w, hw⟩ := D.geometric_evaluateBlock_surjective hg t.multiplierNat (D.fiberFamily b x) (v, false) z
  have hz : (w.val.val t.multiplierNat).val.toMul = z.val.val.toMul :=
    congrArg (fun a => a.val.val.toMul) hw
  rw [← hz]
  let e := D.c46FiberIsogeny hIsogenyQuotient t x (c.val ≫ (D.correspondence t).target) c.val c.property rfl
  let f := D.c46FiberIsogeny hIsogenyQuotient t x (d.val ≫ (D.correspondence t).target) d.val d.property rfl
  have he := D.framedBlock_mem_iff_kernel hg e frame hf D.reference.polarizationType
    (D.fiberPolarizationType hgeometry b x) hg.2.2.2.2 t.multiplierNat (v, false) w
  have hd := D.framedBlock_mem_iff_kernel hg f frame hf D.reference.polarizationType
    (D.fiberPolarizationType hgeometry b x) hg.2.2.2.2 t.multiplierNat (v, false) w
  apply he.symm.trans
  have hv : Rational.framedTateLattice frame e.isogeny.hom (v, false) =
      Rational.framedTateLattice frame f.isogeny.hom (v, false) := congrFun h v
  rw [hv]
  exact hd

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
