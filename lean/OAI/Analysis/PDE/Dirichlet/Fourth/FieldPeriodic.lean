import OAI.Analysis.PDE.Dirichlet.Fourth.FieldEquation
import OAI.Analysis.PDE.Dirichlet.Periodic.HigherJet
import OAI.Analysis.PDE.Elliptic.Boundary.TangentField
import OAI.Analysis.Normed.Function.Holder.C2HolderLattice

/-! Periodic second tangent derivatives have genuine Hölder forcing without
assuming Hölder regularity of the fourth derivative. -/

noncomputable section
open Set Module Filter
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

omit [Fintype ι] in
theorem LatticePeriodic.fieldDerivative {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    {u : E → ℝ} {T : E → E} (hu : LatticePeriodic e b u) (hT : LatticePeriodic e b T) :
    LatticePeriodic e b (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) := by
  intro x l
  unfold OAI.Analysis.PDE.Elliptic.fieldDerivative
  rw [hu.fderiv x l, hT x l]

theorem fieldDerivative_zero_on_level [CompleteSpace E]
    {r u : E → ℝ} {T : E → E} (hr : ContDiff ℝ 1 r) (hu : Differentiable ℝ u)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hzero : ∀ x, r x = 0 → u x = 0)
    (hT : ∀ x, r x = 0 → fderiv ℝ r x (T x) = 0)
    {x : E} (hx : r x = 0) : OAI.Analysis.PDE.Elliptic.fieldDerivative u T x = 0 := by
  apply level_set_derivative_zero (hr.contDiffAt.hasStrictFDerivAt one_ne_zero)
    (hreg x hx) (hu x).hasFDerivAt
  · filter_upwards [] with y hy
    exact hzero y (hy.trans hx)
  · exact hT x hx

theorem twice_fieldDerivative_zero_on_level [CompleteSpace E]
    {r u : E → ℝ} {T S : E → E} (hr : ContDiff ℝ 1 r) (hu : ContDiff ℝ 2 u)
    (hTc : ContDiff ℝ 1 T) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hzero : ∀ x, r x = 0 → u x = 0)
    (hT : ∀ x, r x = 0 → fderiv ℝ r x (T x) = 0)
    (hS : ∀ x, r x = 0 → fderiv ℝ r x (S x) = 0)
    {x : E} (hx : r x = 0) :
    OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) S x = 0 := by
  apply fieldDerivative_zero_on_level hr
    ((OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative hu hTc (by norm_num)).differentiable one_ne_zero) hreg
    (fun y hy => fieldDerivative_zero_on_level hr (hu.differentiable (by norm_num))
      hreg hzero hT hy) hS hx

section Indexed
variable {I : Type*} [Fintype I] [DecidableEq I]
  {e : EuclideanSpace ℝ I ≃L[ℝ] P × V} {b : Basis ι ℝ P}

omit [Fintype ι] in
theorem periodic_indexedNondivergence {A : EuclideanSpace ℝ I → Matrix I I ℝ}
    {u : EuclideanSpace ℝ I → ℝ} (hA : LatticePeriodic e b A) (hu : LatticePeriodic e b u) :
    LatticePeriodic e b (indexedNondivergenceOperator A u) := by
  intro x l
  unfold indexedNondivergenceOperator
  rw [hA x l, hu.fderiv.fderiv x l]

omit [Fintype ι] in
theorem periodic_indexedFieldCorrection {A : EuclideanSpace ℝ I → Matrix I I ℝ}
    {u : EuclideanSpace ℝ I → ℝ} {T : EuclideanSpace ℝ I → EuclideanSpace ℝ I}
    (hA : LatticePeriodic e b A) (hu : LatticePeriodic e b u) (hT : LatticePeriodic e b T) :
    LatticePeriodic e b (indexedFieldCorrection A u T) := by
  intro x l
  unfold indexedFieldCorrection
  rw [hA x l, hu.fderiv x l, hu.fderiv.fderiv x l, hT.fderiv x l, hT.fderiv.fderiv x l]

omit [Fintype ι] in
theorem periodic_indexedFieldCommutator {A : EuclideanSpace ℝ I → Matrix I I ℝ}
    {u : EuclideanSpace ℝ I → ℝ} {T : EuclideanSpace ℝ I → EuclideanSpace ℝ I}
    (hA : LatticePeriodic e b A) (hu : LatticePeriodic e b u) (hT : LatticePeriodic e b T) :
    LatticePeriodic e b (indexedFieldCommutator A u T) := by
  have hd : LatticePeriodic e b (fun y i j => OAI.Analysis.PDE.Elliptic.fieldDerivative (fun z => A z i j) T y) := by
    intro x l
    funext i j
    exact ((hA.comp (fun a => a i j)).fieldDerivative hT) x l
  intro x l
  unfold indexedFieldCommutator
  rw [periodic_indexedFieldCorrection hA hu hT x l, periodic_indexedNondivergence hd hu x l]

end Indexed

section Moore
variable {n : ℕ} {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}

omit [Fintype ι] in
theorem periodic_mooreSecondFieldForcing {u f : CoordinateSpace n 4 → ℝ}
    {T S : CoordinateSpace n 4 → CoordinateSpace n 4}
    (hu : LatticePeriodic e b u) (hf : LatticePeriodic e b f)
    (hT : LatticePeriodic e b T) (hS : LatticePeriodic e b S) :
    LatticePeriodic e b (mooreSecondFieldForcing u f T S) := by
  have hA := (hu.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).comp mooreRealMatrix
  have hfirst : LatticePeriodic e b (mooreFirstFieldForcing u f T) :=
    (hf.fieldDerivative hT).add (periodic_indexedFieldCorrection hA hu hT)
  exact (hfirst.fieldDerivative hS).add
    (periodic_indexedFieldCommutator hA (hu.fieldDerivative hT) hS)

theorem exists_periodic_second_field_forcing
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r : CoordinateSpace n 4 → ℝ}
    (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (u f : CoordinateSpace n 4 → ℝ) (T S : CoordinateSpace n 4 → CoordinateSpace n 4)
    (hu : ContDiff ℝ 4 u) (hf : ContDiff ℝ 3 f)
    (hT : ContDiff ℝ 4 T) (hS : ContDiff ℝ 3 S)
    (hup : LatticePeriodic e b u) (hfp : LatticePeriodic e b f)
    (hTp : LatticePeriodic e b T) (hSp : LatticePeriodic e b S)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ F : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} ℝ α,
      ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value F x = mooreSecondFieldForcing u f T S x :=
  exists_periodic_holder_field e b hK hr hrp hbounded _
    (contDiff_mooreSecondFieldForcing u f T S hu hf hT hS)
    (periodic_mooreSecondFieldForcing hup hfp hTp hSp) hα hα1

end Moore
end OAI.Analysis.PDE.Dirichlet
