import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenKernelLattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricSplitFrame

/-! # Chosen Kernel Targets -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenKernelTargets.CM

noncomputable section

/-! The full PEL target of a fixed-multiplier isogeny is determined by
its chosen kernels. The opposite lattices follow from the actual
polarization, and the moduli-point equality follows from full PEL
quotient uniqueness. The source frame is constructed from its geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) {k : Type} [Field k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} {m : ℕ}
  (x y z : D.GeometricPoint b)
  (e : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ m))
  (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b z) (q ^ m))
  (hker : ∀ v : Fin s,
    (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel e.isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock (D.fiberFamily b x) (D.localCharacter (v, false)) m) =
    (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock (D.fiberFamily b x) (D.localCharacter (v, false)) m))

include hg hgeometry hker in
theorem chosen_lattices_eq (frame : D.FiberFrame b x)
    (hf : AbelianScheme.TateComparison.Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)
    (v : Fin s) : AbelianScheme.TateComparison.Rational.framedTateLattice frame e.isogeny.hom (v, false) =
      AbelianScheme.TateComparison.Rational.framedTateLattice frame f.isogeny.hom (v, false) := by
  apply ChosenKernelLattices.CM.lattice_eq_of_block_kernel D hg e f frame hf
    D.reference.polarizationType (D.fiberPolarizationType hgeometry b x) hg.2.2.2.2
  intro w
  let t := D.evaluateBlock hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) m (v, false) w
  have hb := (D.torsionBlock_mem_iff hg (Over.mk (𝟙 (Spec (.of k))))
    (D.fiberFamily b x) m (v, false) t.val).mp t.property
  have he := congrArg (fun H : AbelianScheme.TateComparison.Subgroups.PointSubgroup (D.fiberFamily b x).abelian =>
    (w.val.val m).val.toMul ∈ H.atTest (Over.mk (𝟙 (Spec (.of k))))) (hker v)
  exact (and_iff_left hb).symm.trans ((iff_of_eq he).trans (and_iff_left hb))

include hg hgeometry hker in
theorem target_eq_in_frame (frame : D.FiberFrame b x)
    (hf : AbelianScheme.TateComparison.Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame) :
    y = z := by
  let : CharZero k := AbelianScheme.TateComparison.FiberLattices.charZero_of_field_spec_map b
  have hc := chosen_lattices_eq D hg hgeometry x y z e f hker frame hf
  apply D.geometricTarget_eq_of_preimage_eq hg hgeometry x y z e f
  apply D.preimage_eq_of_framedTateLattice_eq hg e frame hf D.reference.polarizationType
    (D.fiberPolarizationType hgeometry b x) hg.2.2.2.2 f
  rintro ⟨v, side⟩
  cases side
  · exact hc v
  · rw [D.geometricIsogeny_opposite_lattice hg hgeometry frame hf e,
      D.geometricIsogeny_opposite_lattice hg hgeometry frame hf f, hc v]

include hg hgeometry hker in
theorem target_eq (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s) : y = z :=
  target_eq_in_frame D hg hgeometry x y z e f hker
    (D.geometricSplitFrame hg hdegree hs hgeometry b x)
    (D.geometricSplitFrame_equivariant hg hdegree hs hgeometry b x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenKernelTargets.CM
