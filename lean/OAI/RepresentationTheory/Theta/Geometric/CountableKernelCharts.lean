import OAI.RepresentationTheory.Theta.Geometric.PartialKernelCoordinates
import Mathlib.Topology.Compactness.Lindelof

/-! # Countable Kernel Charts -/

namespace OAI.RepresentationTheory.Theta.Geometric.CountableKernelCharts

noncomputable section

/-! A holomorphic matrix has countably many local coordinate patches
covering every parameter where its kernel is a normalized line. -/

open Set

theorem exists_countable_kernel_coordinate_charts
    {S W : Type} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (p : S → Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] W) (U : Set S) (hU : IsOpen U)
    (hp : DifferentiableOn ℂ p U) :
    ∃ I : Type, Countable I ∧ ∃ (O : I → Set S) (period : I → S → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      (∀ i, IsOpen (O i) ∧ O i ⊆ U ∧ DifferentiableOn ℂ (period i) (O i)) ∧
      ∀ q ∈ U, ∀ z : Geometry.ComplexBall.PrescribedSignsB.BallChart, (p q).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} →
        ∃ i, q ∈ O i ∧ period i q = z := by
  let good : Set S := {q | q ∈ U ∧ ∃ z : Geometry.ComplexBall.PrescribedSignsB.BallChart, (p q).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}}
  have hex (q : good) : ∃ (O : Set S) (period : S → Geometry.ComplexBall.PrescribedSignsB.BallChart), IsOpen O ∧ q.val ∈ O ∧ O ⊆ U ∧
      DifferentiableOn ℂ period O ∧
      ∀ a ∈ O, ∀ z : Geometry.ComplexBall.PrescribedSignsB.BallChart, p a (Geometry.ComplexBall.PrescribedSignsB.lineVector z) = 0 → period a = z := by
    obtain ⟨z, hz⟩ := q.property.2
    exact PartialKernelCoordinates.exists_holomorphic_partial_kernel_coordinate p U hU hp q.val q.property.1 z hz
  choose O period hO hqO hOU hhol hmatch using hex
  obtain ⟨J, hJ, hcover⟩ := (HereditarilyLindelofSpace.isLindelof good).elim_countable_subcover
    O hO (fun q hq => mem_iUnion.mpr ⟨⟨q, hq⟩, hqO ⟨q, hq⟩⟩)
  refine ⟨J, hJ.to_subtype, fun i => O i.val, fun i => period i.val,
    fun i => ⟨hO i.val, hOU i.val, hhol i.val⟩, ?_⟩
  intro q hq z hz
  obtain ⟨i, hqi⟩ := mem_iUnion.mp (hcover (show q ∈ good from ⟨hq, z, hz⟩))
  obtain ⟨hi, hqi⟩ := mem_iUnion.mp hqi
  refine ⟨⟨i, hi⟩, hqi, hmatch i q hqi z ?_⟩
  change Geometry.ComplexBall.PrescribedSignsB.lineVector z ∈ (p q).ker
  rw [hz]
  exact Submodule.mem_span_singleton_self _

end

end OAI.RepresentationTheory.Theta.Geometric.CountableKernelCharts
