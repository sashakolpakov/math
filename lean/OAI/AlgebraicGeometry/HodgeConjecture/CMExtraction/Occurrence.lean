import OAI.LinearAlgebra.Endomorphisms.Commuting
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters

/-! # Occurrence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Occurrence.Spectral

noncomputable section

/-! Occurrence at the fixed complex embedding descends to the algebraic
coefficient field. The full spectral decomposition preserves generalized
multiplicities; no diagonalizability assumption is used. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Extension

variable {U J : Type*} [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U]

theorem complex_joint_occurrence_descends (F : IntermediateField ℚ ℂ) [IsAlgClosed F]
    (T : J → Module.End ℚ U) (hcomm : ∀ h k, Commute (T h) (T k)) (χ : J → F)
    (hχ : HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) (fun h => (χ h : ℂ)) ≠ ⊥) :
    HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange F) χ ≠ ⊥ := by
  let TF : J → Module.End F (F ⊗[ℚ] U) := fun h => (T h).baseChange F
  have hTF (h k : J) : Commute (TF h) (TF k) := by
    change (T h).baseChange F * (T k).baseChange F = (T k).baseChange F * (T h).baseChange F
    simpa only [LinearMap.baseChange_mul] using congrArg (fun f : Module.End ℚ U => f.baseChange F)
      (hcomm h k).eq
  obtain ⟨_, _, _, hfinite, hind, hspan, _⟩ := LinearAlgebra.Endomorphisms.Commuting.Construction.commuting_family_structure TF hTF
  let O := {ψ : J → F // HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace TF ψ ≠ ⊥}
  let : Fintype O := hfinite.fintype
  let ψ : O → J → F := fun i => i.val
  have hS : DirectSum.IsInternal (fun i : O => HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace TF (ψ i)) :=
    HeckeCycles.HeckeCharacters.CM.Projectors.joint_internal_of_Commuting TF hind hspan
  let Q := HeckeCycles.ScalarConjugate.CM.Extension.extendedProjector F U TF ψ hS
  have hQcomm (i : O) (h : J) : Commute (Q i) ((T h).baseChange ℂ) := by
    simpa only [TF, HeckeCycles.ScalarConjugate.CM.Extension.extendEnd_rational] using HeckeCycles.ScalarConjugate.CM.Extension.extendedProjector_commutes F U TF ψ hS hTF i h
  have hQrange (i : O) : LinearMap.range (Q i) ≤
      HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) (fun h => (ψ i h : ℂ)) := by
    simpa only [TF, HeckeCycles.ScalarConjugate.CM.Extension.extendEnd_rational] using HeckeCycles.ScalarConjugate.CM.Extension.extendedProjector_range_le F U TF ψ hS i
  intro hbot
  apply hχ
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  have hz (i : O) : Q i x = 0 := by
    have hne : (fun h => (ψ i h : ℂ)) ≠ (fun h => (χ h : ℂ)) := by
      intro he
      have heF : i.val = χ := funext fun h => Subtype.ext (congrFun he h)
      exact i.property (heF.symm ▸ hbot)
    have ha := hQrange i (LinearMap.mem_range_self (Q i) x)
    have hb := HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace_stable_of_commutes (fun h => (T h).baseChange ℂ)
      (fun h => (χ h : ℂ)) (Q i) (fun h => (hQcomm i h).symm) hx
    exact Submodule.disjoint_def.mp (HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace_disjoint _ hne) _ ha hb
  have hs := HeckeCycles.ScalarConjugate.CM.Extension.sum_extendedProjector F U TF ψ hS x
  change ∑ i, Q i x = x at hs
  simpa only [hz, Finset.sum_const_zero] using hs.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Occurrence.Spectral
