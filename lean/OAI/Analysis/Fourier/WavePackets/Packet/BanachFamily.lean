import OAI.Analysis.Fourier.WavePackets.Packet.Existence
import OAI.Analysis.Fourier.WavePackets.Dirichlet.ParameterFamily

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Module Filter OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped ContDiff Topology Matrix.Norms.Elementwise

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n + 1) → ℝ}
  {lam : ℝ} {z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} {α : ℝ}

attribute [local instance] OAI.Analysis.PDE.Schauder.latticeJetsDualGroup OAI.Analysis.PDE.Schauder.latticeJetsDualSpace
  OAI.Analysis.PDE.Schauder.latticeJetsSecondGroup OAI.Analysis.PDE.Schauder.latticeJetsSecondSpace

local instance packetHolderGroup (I : PacketInitialization R h a ha κ cR cI v lam z₀ α) :
    NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ)
      (fun x (hx : I.data.defining x < 0) => (show I.data.defining x ≤ 0 from hx.le)) α) :=
  OAI.Analysis.Normed.Function.Holder.instC2HolderNormedAddCommGroup _ _

local instance packetHolderSpace (I : PacketInitialization R h a ha κ cR cI v lam z₀ α) :
    NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ)
      (fun x (hx : I.data.defining x < 0) => (show I.data.defining x ≤ 0 from hx.le)) α) :=
  OAI.Analysis.Normed.Function.Holder.instC2HolderNormedSpace _ _

theorem PacketInitialization.closed_nonempty
    (I : PacketInitialization R h a ha κ cR cI v lam z₀ α) :
    {x | I.data.defining x ≤ 0}.Nonempty := by
  have ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖ :=
    (I.neighborhood (mem_closedBall_self I.radius_pos.le)).1.le
  obtain ⟨x,hx⟩ := paddedPhysicalDefining_nonempty (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha ht
  exact ⟨x,(I.closedDomain x).mpr hx⟩

/-- The literal packet coefficients possess an actual positive smooth
Banach branch near every annulus parameter. No inverse, residual identity,
or base-point jet is an extra hypothesis. -/
theorem PacketInitialization.exists_positive_banach_family
    (I : PacketInitialization R h a ha κ cR cI v lam z₀ α)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ (w : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace
      (hΩK := fun x (hx : I.data.defining x < 0) => (show I.data.defining x ≤ 0 from hx.le))
      (α := α) (paddedPhysicalSplit (n + 1))
      (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))) (W : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)),
      IsOpen W ∧ z₀ ∈ W ∧ W ⊆ ball z₀ I.radius ∧ ContDiffOn ℝ ∞ w W ∧
      (∀ x : {x | I.data.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value (w z₀).val x = I.solution.u x) ∧
      ∀ z ∈ W,
        I.fields.analytic.periodicOperator I.lifts I.data.defining_periodic hα.le (z,w z) = 0 ∧
        I.fields.analytic.PositiveAt I.lifts hα.le (z,w z) := by
  let : Nonempty {x | I.data.defining x ≤ 0} := I.closed_nonempty.to_subtype
  have h0 : z₀ ∈ ball z₀ I.radius := mem_ball_self I.radius_pos
  have ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖ :=
    (I.neighborhood (mem_closedBall_self I.radius_pos.le)).1.le
  have hrl : ∀ x, I.data.defining x ≤ 0 →
      paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0 :=
    fun x hx => (I.closedDomain x).mp hx
  apply I.solution.exists_positive_parameter_family I.fields.analytic I.lifts hα hα1 isOpen_ball h0
  · intro x
    rw [I.fields.jacobian_base ht h0 hrl]
    rfl
  · intro x
    rw [I.fields.curvature_base ht h0 hrl]
    rfl
  · intro x
    rw [I.background]
    exact I.fields.background_base_value ht h0 hrl x
  · intro x
    rw [I.source]
    exact I.fields.source_base_value ht h0 hrl x

end OAI.Analysis.Fourier.WavePackets
