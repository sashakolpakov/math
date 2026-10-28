import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalKernelNilpotence
import Mathlib.CategoryTheory.ObjectProperty.Extensions

/-! # Coherent Nilpotent Induction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentNilpotentInduction

noncomputable section

/-! Coherent induction through the constructed nilpotent layers, and
reduction of a property on a closed support to its actual closed subscheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem coherent_nilpotent_induction
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P : ObjectProperty X.Modules) [P.IsClosedUnderExtensions]
    (I : X.IdealSheafData)
    (hlayer : ∀ (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType],
      I ≤ CoherentAnnihilator.coherentAnnihilator M → P M)
    (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (h : I ^ n ≤ CoherentAnnihilator.coherentAnnihilator M) : P M := by
  induction n generalizing M with
  | zero =>
      apply hlayer M
      apply le_trans (show I ≤ I ^ 0 from by simp) h
  | succ n ih =>
      let f := I.subschemeι
      let K := ClosedReductionLayer.closedReductionKernel f M
      let Q := ClosedReductionLayer.closedReductionQuotient f M
      have : K.IsQuasicoherent := ClosedReductionLayer.closedReductionKernel_quasicoherent f M
      have : K.IsFiniteType := ClosedReductionLayer.closedReductionKernel_finiteType f M
      have : Q.IsQuasicoherent := ClosedReductionLayer.closedReductionQuotient_quasicoherent f M
      have : Q.IsFiniteType := ClosedReductionLayer.closedReductionQuotient_finiteType f M
      have hn : f.ker ^ (n + 1) ≤ CoherentAnnihilator.coherentAnnihilator M := by
        simpa only [f, I.ker_subschemeι] using h
      have hK : I ^ n ≤ CoherentAnnihilator.coherentAnnihilator K := by
        simpa only [f, I.ker_subschemeι] using GlobalKernelNilpotence.closedReductionKernel_power_annihilates f M n hn
      have hQ : I ≤ CoherentAnnihilator.coherentAnnihilator Q := by
        simpa only [f, I.ker_subschemeι] using ClosedReductionLayer.closedReductionQuotient_ideal_annihilates f M
      exact P.prop_X₂_of_shortExact (ClosedReductionLayer.closedReductionSequence_shortExact f M)
        (ih K hK) (hlayer Q hQ)

theorem coherent_property_of_closed_support
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (P : ObjectProperty X.Modules) [P.IsClosedUnderExtensions] [P.IsClosedUnderIsomorphisms]
    (I : X.IdealSheafData)
    (hclosed : ∀ (N : I.subscheme.Modules) [N.IsQuasicoherent] [N.IsFiniteType],
      P ((Scheme.Modules.pushforward I.subschemeι).obj N))
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (h : (CoherentAnnihilator.coherentAnnihilator M).support ≤ I.support) : P M := by
  obtain ⟨n, hn⟩ := IdealSheafNilpotence.idealSheaf_exists_power_le_of_support_le I (CoherentAnnihilator.coherentAnnihilator M) h
  apply coherent_nilpotent_induction P I _ n M hn
  intro Q _ _ hQ
  obtain ⟨N, hq, ht, ⟨e⟩⟩ := CoherentClosedDescent.exists_coherent_on_annihilating_subscheme Q I hQ
  let := hq
  let := ht
  exact P.prop_of_iso e (hclosed N)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentNilpotentInduction
