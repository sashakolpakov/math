import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ReductionKernelNilpotence
import Mathlib.CategoryTheory.ObjectProperty.Extensions

/-! # Nilpotent Induction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.NilpotentInduction

noncomputable section

/-! Coherent induction through the constructed nilpotent layers, and
reduction of a property on a closed support to its actual closed subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem coherent_nilpotent_induction
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P : ObjectProperty X.Modules) [P.IsClosedUnderExtensions]
    (I : X.IdealSheafData)
    (hlayer : ∀ (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType],
      I ≤ Annihilator.coherentAnnihilator M → P M)
    (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (h : I ^ n ≤ Annihilator.coherentAnnihilator M) : P M := by
  induction n generalizing M with
  | zero =>
      apply hlayer M
      apply le_trans (show I ≤ I ^ 0 from by simp) h
  | succ n ih =>
      let f := I.subschemeι
      let K := Closed.ReductionLayer.closedReductionKernel f M
      let Q := Closed.ReductionLayer.closedReductionQuotient f M
      have : K.IsQuasicoherent := Closed.ReductionLayer.closedReductionKernel_quasicoherent f M
      have : K.IsFiniteType := Closed.ReductionLayer.closedReductionKernel_finiteType f M
      have : Q.IsQuasicoherent := Closed.ReductionLayer.closedReductionQuotient_quasicoherent f M
      have : Q.IsFiniteType := Closed.ReductionLayer.closedReductionQuotient_finiteType f M
      have hn : f.ker ^ (n + 1) ≤ Annihilator.coherentAnnihilator M := by
        simpa only [f, I.ker_subschemeι] using h
      have hK : I ^ n ≤ Annihilator.coherentAnnihilator K := by
        simpa only [f, I.ker_subschemeι] using Global.ReductionKernelNilpotence.closedReductionKernel_power_annihilates f M n hn
      have hQ : I ≤ Annihilator.coherentAnnihilator Q := by
        simpa only [f, I.ker_subschemeι] using Closed.ReductionLayer.closedReductionQuotient_ideal_annihilates f M
      exact P.prop_X₂_of_shortExact (Closed.ReductionLayer.closedReductionSequence_shortExact f M)
        (ih K hK) (hlayer Q hQ)

theorem coherent_property_of_closed_support
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (P : ObjectProperty X.Modules) [P.IsClosedUnderExtensions] [P.IsClosedUnderIsomorphisms]
    (I : X.IdealSheafData)
    (hclosed : ∀ (N : I.subscheme.Modules) [N.IsQuasicoherent] [N.IsFiniteType],
      P ((Scheme.Modules.pushforward I.subschemeι).obj N))
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (h : (Annihilator.coherentAnnihilator M).support ≤ I.support) : P M := by
  obtain ⟨n, hn⟩ := IdealSheafNilpotence.idealSheaf_exists_power_le_of_support_le I (Annihilator.coherentAnnihilator M) h
  apply coherent_nilpotent_induction P I _ n M hn
  intro Q _ _ hQ
  obtain ⟨N, hq, ht, ⟨e⟩⟩ := ClosedDescent.exists_coherent_on_annihilating_subscheme Q I hQ
  let := hq
  let := ht
  exact P.prop_of_iso e (hclosed N)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.NilpotentInduction
