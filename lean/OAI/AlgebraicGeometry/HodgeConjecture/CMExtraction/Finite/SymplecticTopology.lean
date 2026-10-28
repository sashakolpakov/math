import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompactPrincipalLevel
import Mathlib.Topology.Instances.Matrix

/-! # Symplectic Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.SymplecticTopology.TestTransport

noncomputable section

/-! Continuity of the actual finite symplectic phase action. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

instance finiteSymplecticTopologicalGroup : IsTopologicalGroup (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  continuous_mul := by
    apply Continuous.subtype_mk
    change Continuous (fun p : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf × RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => p.1.val * p.2.val)
    exact (continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply Continuous.subtype_mk
    change Continuous (fun g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => (-Matrix.J I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) * g.val.transpose * Matrix.J I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    exact (continuous_const.matrix_mul continuous_subtype_val.matrix_transpose).matrix_mul continuous_const

variable {X : Type*} [TopologicalSpace X]
  {g : X → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf} {p q : X → (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)}

theorem finitePhase_continuous (hg : Continuous g) (hp : Continuous p) (hq : Continuous q) :
    Continuous (fun x => (g x).val *ᵥ Sum.elim (p x) (q x)) := by
  apply (continuous_subtype_val.comp hg).matrix_mulVec
  apply continuous_pi
  intro i
  cases i with
  | inl i => exact (continuous_apply i).comp hp
  | inr i => exact (continuous_apply i).comp hq

@[fun_prop] theorem finiteMomentum_continuous
    (hg : Continuous g) (hp : Continuous p) (hq : Continuous q) :
    Continuous (fun x => PhaseAction.TestTransport.finiteMomentum (g x) (p x) (q x)) :=
  continuous_pi fun i => (continuous_apply (Sum.inl i)).comp (finitePhase_continuous hg hp hq)

@[fun_prop] theorem finitePosition_continuous
    (hg : Continuous g) (hp : Continuous p) (hq : Continuous q) :
    Continuous (fun x => PhaseAction.TestTransport.finitePosition (g x) (p x) (q x)) :=
  continuous_pi fun i => (continuous_apply (Sum.inr i)).comp (finitePhase_continuous hg hp hq)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.SymplecticTopology.TestTransport
