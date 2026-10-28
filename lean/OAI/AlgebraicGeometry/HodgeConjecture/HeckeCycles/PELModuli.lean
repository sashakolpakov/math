import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELReconstruction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELFamily

/-! # PEL Moduli -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELModuli.CM

noncomputable section

/-! Transfer the full reduced-test-scheme classification from IntegralModel to
TateComparison on the same universal family and the same moduli scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELFamily.CM.Family OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELReconstruction.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELFamily.CM.Isomorphisms

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  {g N : ℕ} {δ : Fin g → ℕ} {S T : Scheme}

omit [NumberField E] [NumberField.IsCMField E] in
theorem family_isomorphism_iff (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S)
    (B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N T) (f : T ⟶ S) :
    Nonempty (PELModuli.IntegralModel.PEL.Has.PulledBackPELDataIso A B f (𝟙 T)) ↔
      Nonempty (AbelianScheme.TateComparison.PELModuli.PELFamilyIso ((PELFamily.CM.Family.ofActionData A).pullback f) (PELFamily.CM.Family.ofActionData B)) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(PELFamily.CM.Isomorphisms.toFamilyIso e).trans (PELFamily.CM.Isomorphisms.familyPullbackId B)⟩
  · rintro ⟨e⟩
    exact ⟨PELFamily.CM.Isomorphisms.fromFamilyIso (e.trans (PELFamily.CM.Isomorphisms.familyPullbackId B).symm)⟩

variable {K : Type} [Field K] [NumberField K]
  {s : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ}

def candidate (V : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N M U B) :
    AbelianScheme.TateComparison.PELModuli.PELModuliCandidate P N B.base where
  space := V.toOver
  family := PELFamily.CM.Family.ofActionData V.universal.data

/-- The full TateComparison classification is derived, including both preservation
under pullback and the unique classifying morphism for every PEL family. -/
theorem classifiesReduced_from_integral
    (V : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N M U B)
    (hV : V.IsReducedPELModuli P) :
    (candidate V).ClassifiesReduced (PELFamily.CM.Family.baseAction (B.integralEmbedding iota)) := by
  constructor
  · intro T _ x
    change T ⟶ V.toOver at x
    have h := PELFamily.CM.Family.integralObject_isPEL (V.universal.pullback x)
    exact (congrArg (AbelianScheme.TateComparison.PELModuli.IsPELFamily P
      (T.hom.appTop.hom.comp (PELFamily.CM.Family.baseAction (B.integralEmbedding iota))))
        (PELFamily.CM.Family.ofActionData_pullback V.universal.data x.left)).mp h
  · intro T _ D hD
    let A := PELReconstruction.CM.toIntegralObject D hD
    have heq : PELFamily.CM.Family.ofActionData A.data = D := PELReconstruction.CM.reconstructed_family D hD
    obtain ⟨x, hx, hunique⟩ := hV T A
    refine ⟨x, ?_, ?_⟩
    · have h := (family_isomorphism_iff V.universal.data A.data x.left).mp hx
      rw [heq] at h
      exact h
    · intro y hy
      apply hunique y
      apply (family_isomorphism_iff V.universal.data A.data y.left).mpr
      rw [heq]
      exact hy

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELModuli.CM
