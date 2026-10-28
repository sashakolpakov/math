import OAI.Analysis.PDE.Dirichlet.Linear.BanachUniqueness
import OAI.Analysis.Normed.Function.Holder.SmoothPeriodicExtensionJets

/-! Identification of a classical solution with a closed-domain Hölder
solution. No Hölder assumption is made on the classical second derivative. -/

noncomputable section
open Set Filter Module
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem moore_classical_eq_banach_value
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) Q)
    (hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hrL : ∀ x, r x < 0 → 0 < mooreLinearization A r x)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hU : U ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat)
    (w : CoordinateSpace n 4 → ℝ)
    (hw : ContDiffOn ℝ 2 w {x | r x < 0})
    (hwc : ContinuousOn w {x | r x ≤ 0}) (hwp : LatticePeriodic e lat w)
    (hwzero : ∀ x, r x = 0 → w x = 0)
    (heq : ∀ x (hx : r x < 0), mooreLinearization A w x =
      OAI.LinearAlgebra.Moore.mooreDifferential n (A x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots U) ⟨x, hΩD hx⟩)) :
    ∀ x : {x | r x ≤ 0}, w x = OAI.Analysis.Normed.Function.Holder.C2Holder.value U x := by
  let v := OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  have hv : ContDiffOn ℝ 2 v {x | r x < 0} := OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ U
  have hL (x) (hx : r x < 0) : mooreLinearization A w x =
      mooreLinearization A v x := by
    dsimp [v]
    simp only [mooreLinearization]
    rw [← quaternionHessianField_eq hΩ hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots U hx]
    exact heq x hx
  have hzero := moore_linearized_zero_continuous_lattice e lat hC hr
    (hw.add (hv.const_smul (-1 : ℝ)))
    (hwc.add ((OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)).const_smul (-1 : ℝ)))
    hrp (hwp.add (hU.2.smul (-1))) hbounded hA
    (by
      intro x hx
      rw [mooreLinearization_add_smul_at A (hw.contDiffAt (hΩ.mem_nhds hx))
        (hv.contDiffAt (hΩ.mem_nhds hx)), hL x hx]
      ring)
    hrL (by
      intro x hx
      have hb : v x = 0 := by
        dsimp [v]
        rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) hx.le]
        exact hU.1 ⟨x, hx.le⟩ (by simp only [Set.mem_ofPred_eq, hx, lt_self_iff_false,
          not_false_eq_true])
      simp only [hwzero x hx, hb, smul_zero, add_zero])
  intro x
  have hz := hzero x x.property
  change w x + (-1 : ℝ) * v x = 0 at hz
  dsimp [v] at hz
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property] at hz
  linarith

theorem moore_classical_eq_banach_jets
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) Q)
    (hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hrL : ∀ x, r x < 0 → 0 < mooreLinearization A r x)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hU : U ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat)
    (w : CoordinateSpace n 4 → ℝ) (hw : ContDiff ℝ 2 w)
    (hwp : LatticePeriodic e lat w) (hwzero : ∀ x, r x = 0 → w x = 0)
    (heq : ∀ x (hx : r x < 0), mooreLinearization A w x =
      OAI.LinearAlgebra.Moore.mooreDifferential n (A x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots U) ⟨x, hΩD hx⟩)) :
    (∀ x : {x | r x ≤ 0}, w x = OAI.Analysis.Normed.Function.Holder.C2Holder.value U x) ∧
    (∀ x : {x | r x ≤ 0}, fderiv ℝ w x = OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x) ∧
    (∀ x : {x | r x ≤ 0}, fderiv ℝ (fderiv ℝ w) x = OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x) := by
  have hvalue := moore_classical_eq_banach_value e lat hC hr hrp hbounded A hA hrL
    U hU w hw.contDiffOn hw.continuous.continuousOn hwp hwzero heq
  exact ⟨hvalue, OAI.Analysis.Normed.Function.Holder.C2Holder.classical_extension_derivatives
    (isOpen_lt hr.continuous continuous_const) hclosure U w hw hvalue⟩

end OAI.Analysis.PDE.Dirichlet
