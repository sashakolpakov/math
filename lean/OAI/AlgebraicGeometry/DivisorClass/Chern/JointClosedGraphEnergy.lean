import OAI.AlgebraicGeometry.DivisorClass.Chern.HilbertTripleSq
import Mathlib.Topology.Algebra.Module.LinearPMap

/-! # Joint Closed Graph Energy -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.JointClosedGraphEnergy

noncomputable section

/-! A Hilbert energy space recording two actual closed operator graphs with a common source. -/

variable {A B C H : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup C] [InnerProductSpace ℂ C]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  (T : A →ₗ.[ℂ] B) (S : H →ₗ.[ℂ] C) (j : A →L[ℂ] H)

def jointEnergyFirstGraph : HilbertTripleSq.HilbertTriple A B C →L[ℂ] A × B :=
  (HilbertTripleSq.hilbertTripleFirst A B C).prod (HilbertTripleSq.hilbertTripleSecond A B C)

def jointEnergySecondGraph : HilbertTripleSq.HilbertTriple A B C →L[ℂ] H × C :=
  (j.comp (HilbertTripleSq.hilbertTripleFirst A B C)).prod (HilbertTripleSq.hilbertTripleThird A B C)

def jointEnergySubmodule : Submodule ℂ (HilbertTripleSq.HilbertTriple A B C) :=
  T.graph.comap (jointEnergyFirstGraph (A := A) (B := B) (C := C)).toLinearMap ⊓
    S.graph.comap (jointEnergySecondGraph (B := B) (C := C) j).toLinearMap

abbrev JointEnergy := jointEnergySubmodule T S j

theorem jointEnergy_isClosed (hT : T.IsClosed) (hS : S.IsClosed) :
    IsClosed (jointEnergySubmodule T S j : Set (HilbertTripleSq.HilbertTriple A B C)) :=
  (hT.preimage (jointEnergyFirstGraph (A := A) (B := B) (C := C)).continuous).inter
    (hS.preimage (jointEnergySecondGraph (B := B) (C := C) j).continuous)

theorem jointEnergy_completeSpace [CompleteSpace A] [CompleteSpace B] [CompleteSpace C]
    (hT : T.IsClosed) (hS : S.IsClosed) : CompleteSpace (JointEnergy T S j) :=
  (jointEnergy_isClosed T S j hT hS).completeSpace_coe

def jointEnergySource : JointEnergy T S j →L[ℂ] A :=
  (HilbertTripleSq.hilbertTripleFirst A B C).comp (jointEnergySubmodule T S j).subtypeL

def jointEnergyFirstValue : JointEnergy T S j →L[ℂ] B :=
  (HilbertTripleSq.hilbertTripleSecond A B C).comp (jointEnergySubmodule T S j).subtypeL

def jointEnergySecondValue : JointEnergy T S j →L[ℂ] C :=
  (HilbertTripleSq.hilbertTripleThird A B C).comp (jointEnergySubmodule T S j).subtypeL

theorem jointEnergy_inner (v w : JointEnergy T S j) :
    inner ℂ v w = inner ℂ (jointEnergySource T S j v) (jointEnergySource T S j w) +
      inner ℂ (jointEnergyFirstValue T S j v) (jointEnergyFirstValue T S j w) +
      inner ℂ (jointEnergySecondValue T S j v) (jointEnergySecondValue T S j w) :=
  HilbertTripleSq.hilbertTriple_inner A B C v.val w.val

theorem jointEnergy_norm_sq (v : JointEnergy T S j) :
    ‖v‖ ^ 2 = ‖jointEnergySource T S j v‖ ^ 2 + ‖jointEnergyFirstValue T S j v‖ ^ 2 +
      ‖jointEnergySecondValue T S j v‖ ^ 2 := HilbertTripleSq.hilbertTriple_norm_sq A B C v.val

theorem jointEnergySource_norm (v : JointEnergy T S j) : ‖jointEnergySource T S j v‖ ≤ ‖v‖ := by
  have h := jointEnergy_norm_sq T S j v
  nlinarith [norm_nonneg v, norm_nonneg (jointEnergySource T S j v),
    sq_nonneg ‖jointEnergyFirstValue T S j v‖, sq_nonneg ‖jointEnergySecondValue T S j v‖]

theorem jointEnergy_first_graph (v : JointEnergy T S j) :
    (jointEnergySource T S j v, jointEnergyFirstValue T S j v) ∈ T.graph := v.property.1

theorem jointEnergy_second_graph (v : JointEnergy T S j) :
    (j (jointEnergySource T S j v), jointEnergySecondValue T S j v) ∈ S.graph := v.property.2

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

def jointEnergyLift (a : U →ₗ[ℂ] A) (b : U →ₗ[ℂ] B) (c : U →ₗ[ℂ] C)
    (hT : ∀ u, (a u, b u) ∈ T.graph) (hS : ∀ u, (j (a u), c u) ∈ S.graph) : U →ₗ[ℂ] JointEnergy T S j :=
  ((HilbertTripleSq.hilbertTripleCoordinates A B C).symm.toLinearMap.comp (a.prod (b.prod c))).codRestrict _
    fun u => ⟨hT u, hS u⟩

theorem jointEnergySource_lift (a : U →ₗ[ℂ] A) (b : U →ₗ[ℂ] B) (c : U →ₗ[ℂ] C)
    (hT : ∀ u, (a u, b u) ∈ T.graph) (hS : ∀ u, (j (a u), c u) ∈ S.graph) (u : U) :
    jointEnergySource T S j (jointEnergyLift T S j a b c hT hS u) = a u := rfl

theorem jointEnergyFirstValue_lift (a : U →ₗ[ℂ] A) (b : U →ₗ[ℂ] B) (c : U →ₗ[ℂ] C)
    (hT : ∀ u, (a u, b u) ∈ T.graph) (hS : ∀ u, (j (a u), c u) ∈ S.graph) (u : U) :
    jointEnergyFirstValue T S j (jointEnergyLift T S j a b c hT hS u) = b u := rfl

theorem jointEnergySecondValue_lift (a : U →ₗ[ℂ] A) (b : U →ₗ[ℂ] B) (c : U →ₗ[ℂ] C)
    (hT : ∀ u, (a u, b u) ∈ T.graph) (hS : ∀ u, (j (a u), c u) ∈ S.graph) (u : U) :
    jointEnergySecondValue T S j (jointEnergyLift T S j a b c hT hS u) = c u := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.JointClosedGraphEnergy
