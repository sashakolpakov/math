import OAI.AlgebraicTopology.Cohomology.Singular.ChartBalls
import Mathlib.Topology.Homotopy.LocallyContractible

/-! # Chart Local Contractible -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ChartLocalContractible

noncomputable section

/-!
# Local contractibility from genuine manifold charts

The chart-ball neighborhood basis supplies strong local contractibility
for every space charted on a real normed vector space. In particular,
local path connectedness and classical local contractibility are proved
consequences of the chart structure. They are not extra hypotheses.

The model space is an explicit argument, so users can install the proved
class values locally without asking typeclass inference to guess a model.
-/

open Filter
open scoped _root_.Topology

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (X : Type) [TopologicalSpace X] [ChartedSpace E X]

include E

/-- A real normed model gives a basis of contractible chart neighborhoods. -/
theorem stronglyLocallyContractibleSpace_of_chartedSpace :
    StronglyLocallyContractibleSpace X := by
  refine StronglyLocallyContractibleSpace.of_bases
    (fun x => ChartBalls.nhds_basis_chartBall E x) ?_
  intro x r hr
  exact ChartBalls.contractibleSpace_chartBall E x r hr.1 hr.2

/-- In particular, the inclusions of sufficiently small neighborhoods into
any prescribed neighborhood are null-homotopic. -/
theorem locallyContractibleSpace_of_chartedSpace : LocallyContractibleSpace X := by
  let := stronglyLocallyContractibleSpace_of_chartedSpace E X
  exact StronglyLocallyContractibleSpace.locallyContractible

/-- Local path connectedness follows from the actual chart contractions. -/
theorem locallyPathConnectedSpace_of_chartedSpace : LocallyPathConnectedSpace X := by
  let := stronglyLocallyContractibleSpace_of_chartedSpace E X
  infer_instance

/-- There is in fact a basis of open contractible neighborhoods, a stronger
property than the class of strongly locally contractible spaces requires. -/
theorem openContractible_basis_of_chartedSpace (x : X) :
    (𝓝 x).HasBasis
      (fun U : TopologicalSpace.Opens X => x ∈ U ∧ ContractibleSpace U)
      (fun U => (U : Set X)) := by
  refine ⟨fun s => ⟨?_, ?_⟩⟩
  · intro hs
    obtain ⟨U, hx, hsub, hc⟩ := ChartBalls.exists_contractible_open_subset_of_mem_nhds E x hs
    exact ⟨U, ⟨hx, hc⟩, hsub⟩
  · rintro ⟨U, ⟨hx, _⟩, hsub⟩
    exact mem_of_superset (U.isOpen.mem_nhds hx) hsub

/-- Every open subspace inherits strong local contractibility from the
real normed chart model. -/
theorem stronglyLocallyContractibleSpace_opens_of_chartedSpace
    (U : TopologicalSpace.Opens X) : StronglyLocallyContractibleSpace U := by
  let := stronglyLocallyContractibleSpace_of_chartedSpace E X
  exact U.isOpen.stronglyLocallyContractibleSpace

/-- Every open subspace inherits local path connectedness without an
additional local-connectivity hypothesis. -/
theorem locallyPathConnectedSpace_opens_of_chartedSpace
    (U : TopologicalSpace.Opens X) : LocallyPathConnectedSpace U := by
  let := stronglyLocallyContractibleSpace_opens_of_chartedSpace E X U
  infer_instance

end

end OAI.AlgebraicTopology.Cohomology.Singular.ChartLocalContractible
