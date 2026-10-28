import OAI.Analysis.Fourier.WavePackets.Packet.FlowFields
import OAI.Analysis.Fourier.WavePackets.Dirichlet.ParameterFamily

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation OAI.Analysis.PDE.Green OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped ContDiff

variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n + 1) → ℝ}
  {lam : ℝ} {z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} {α : ℝ} {U C : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)}
local notation "e" => paddedPhysicalSplit (n + 1)
local notation "b" => paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)
variable {D₀ : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b}
attribute [local instance] OAI.Analysis.PDE.Schauder.latticeJetsDualGroup OAI.Analysis.PDE.Schauder.latticeJetsDualSpace
  OAI.Analysis.PDE.Schauder.latticeJetsSecondGroup OAI.Analysis.PDE.Schauder.latticeJetsSecondSpace
local instance flowHolderGroup (Q : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b) :
    NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ)
      (fun x (hx : Q.defining x < 0) => (show Q.defining x ≤ 0 from hx.le)) α) :=
  OAI.Analysis.Normed.Function.Holder.instC2HolderNormedAddCommGroup _ _
local instance flowHolderSpace (Q : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b) :
    NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ)
      (fun x (hx : Q.defining x < 0) => (show Q.defining x ≤ 0 from hx.le)) α) :=
  OAI.Analysis.Normed.Function.Holder.instC2HolderNormedSpace _ _

/-- Genuine smooth fiber solvability supplies the actual Banach base point
for the combined external-parameter and internal spatial-flow family. -/
theorem PacketFlowFields.nonempty_classicalParameterBase
    {A : PacketSmoothCoefficients R h a ha κ cR cI v lam z₀ C}
    {D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b D₀.defining}
    (F : PacketFlowFields A D U α) (S : PeriodicQuaternionicSolution D₀)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts (n := n + 2)
      (P := (Fin (n + 2) → ℝ) × (Fin (n + 2) → ℝ))
      (V := Option (Fin (n + 1)) → ℂ) (r := D₀.defining)
      (fun x (hx : D₀.defining x < 0) => (show D₀.defining x ≤ 0 from hx.le)) α
      (paddedPhysicalSplit (n + 1))
      (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)))
    (hα : 0 < α) :
    α < 1 → z₀ ∈ U → z₀ ∈ C → a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖ →
    (∀ x, D₀.defining x ≤ 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0) →
    (D₀.background = fun x => packetPaddedBackground n a ha lam (z₀,x)) →
    (D₀.density = fun x => packetPaddedSource R h a ha κ cR cI v lam (z₀,x)) →
    Nonempty (ClassicalParameterBase S F.analytic J hα.le (z₀,(0:T))) :=
  fun hα1 hzU hzC hz₀ hrc hB hF =>
  let hrl : ∀ x, D₀.defining x ≤ 0 →
      paddedPhysicalDefining (n + 1) a (energyComplexTime z₀) x ≤ 0 :=
    fun x hx => (hrc x).mp hx
  S.nonempty_parameter_base F.analytic J hα.le hα1.le
    (show (z₀,(0:T)) ∈ U ×ˢ {t : T | ‖t‖ < D.radius} from
      ⟨hzU, (norm_zero : ‖(0 : T)‖ = 0).trans_lt D.radius_pos⟩)
    (fun x => (F.base_values hzU hzC hz₀ hrl x).1)
    (fun x => (F.base_values hzU hzC hz₀ hrl x).2.1)
    (fun x => (F.base_values hzU hzC hz₀ hrl x).2.2.1.trans
      (congrArg (fun g => fderiv ℝ (fderiv ℝ g) (x : CoordinateSpace (n + 2) 4)) hB).symm)
    (fun x => (F.base_values hzU hzC hz₀ hrl x).2.2.2.trans (congrFun hF x).symm)

end OAI.Analysis.Fourier.WavePackets
