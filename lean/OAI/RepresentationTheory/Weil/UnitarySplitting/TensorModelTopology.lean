import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorUnitary
import OAI.RepresentationTheory.Weil.UnitarySplitting.MatrixFrameAction

/-! # Tensor Model Topology -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.TensorModelTopology.Construction

noncomputable section

/-! Continuity of tensor multiplicity models and their frame transport. -/

open _root_.Matrix
open scoped Kronecker

theorem unitaryReindex_continuous
    {F E I J : Type} [Field F] [NormedField E] [Algebra F E]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (σ : E ≃ₐ[F] E) (e : I ≃ J) (Q : Matrix I I E) : Continuous (TensorUnitary.Construction.unitaryReindex σ e Q) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun g : DualPair.Construction.unitaryGroup σ Q => (g.val : Matrix I I E) (e.symm i) (e.symm j))
    fun_prop
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun g : DualPair.Construction.unitaryGroup σ Q => (g.val⁻¹ : (Matrix I I E)ˣ) (e.symm i) (e.symm j))
    fun_prop

theorem leftTensorUnitary_continuous
    {F E I J : Type} [Field F] [NormedField E] [Algebra F E]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (σ : E ≃ₐ[F] E) (Q : Matrix I I E) (W : Matrix J J E) : Continuous (TensorUnitary.Construction.leftTensorUnitary σ Q W) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun g : DualPair.Construction.unitaryGroup σ Q => (g.val : Matrix I I E) i.1 j.1 * (1 : Matrix J J E) i.2 j.2)
    fun_prop
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun g : DualPair.Construction.unitaryGroup σ Q => (g.val⁻¹ : (Matrix I I E)ˣ) i.1 j.1 * (1 : Matrix J J E) i.2 j.2)
    fun_prop

theorem weightedTensorUnitary_continuous
    {F E : Type} [Field F] [NormedField E] [Algebra F E] {m n : ℕ}
    (σ : E ≃ₐ[F] E) (Q : Matrix (Fin m) (Fin m) E) (a : Fin n → Fˣ) :
    Continuous (TensorUnitary.Construction.weightedTensorUnitary σ Q a) :=
  (unitaryReindex_continuous σ finProdFinEquiv _).comp (leftTensorUnitary_continuous σ Q _)

theorem frameSymplectic_continuous
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E] {m n : ℕ}
    (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (hci : Continuous c.coordinates.symm) :
    Continuous (FrameTransport.Construction.frameSymplectic σ H K c) := by
  have ho : Continuous (fun g : FrameTransport.Construction.StandardSymplectic F (m * n) =>
      ((fun x => g.val x), (fun x => g.val.symm x))) := continuous_induced_dom
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply continuous_pi
    intro x
    change Continuous (fun g : FrameTransport.Construction.StandardSymplectic F (m * n) => c.coordinates.symm (g.val (c.coordinates x)))
    exact hci.comp ((continuous_apply (c.coordinates x)).comp (continuous_fst.comp ho))
  · apply continuous_pi
    intro x
    change Continuous (fun g : FrameTransport.Construction.StandardSymplectic F (m * n) => c.coordinates.symm (g.val.symm (c.coordinates x)))
    exact hci.comp ((continuous_apply (c.coordinates x)).comp (continuous_snd.comp ho))

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.TensorModelTopology.Construction
