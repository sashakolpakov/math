import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ParameterEquivalence

/-! # Parameter Universality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ParameterUniversality

noncomputable section

/-! The specified universal Hilbert family gives unique actual classifying maps on locally noetherian tests, naturally for every test morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T : Over S} [IsLocallyNoetherian T.left] {n : ℕ} {P : Polynomial ℚ}

theorem hilbertUniversalFamily_classifies (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) :
    (ParameterScheme.hilbertUniversalFamily S n P).pullback ((ParameterEquivalence.hilbertParameterEquiv n P F).left) = F :=
  (ParameterEquivalence.hilbertParameterEquiv_inverse n P (ParameterEquivalence.hilbertParameterEquiv n P F)).symm.trans
    ((ParameterEquivalence.hilbertParameterEquiv n P).symm_apply_apply F)

theorem hilbertUniversalFamily_existsUnique (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) :
    ∃! g : T ⟶ ParameterScheme.hilbertParameterScheme S n P, (ParameterScheme.hilbertUniversalFamily S n P).pullback g.left = F := by
  refine ⟨ParameterEquivalence.hilbertParameterEquiv n P F, hilbertUniversalFamily_classifies F, ?_⟩
  intro g hg
  apply (ParameterEquivalence.hilbertParameterEquiv n P).symm.injective
  exact (ParameterEquivalence.hilbertParameterEquiv_inverse n P g).trans
    (hg.trans ((ParameterEquivalence.hilbertParameterEquiv n P).symm_apply_apply F).symm)

theorem hilbertParameterEquiv_natural {V : Over S} [IsLocallyNoetherian V.left]
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) (f : V ⟶ T) :
    ParameterEquivalence.hilbertParameterEquiv n P (F.pullback f.left) = f ≫ ParameterEquivalence.hilbertParameterEquiv n P F := by
  symm
  have h : (ParameterScheme.hilbertUniversalFamily S n P).pullback ((f ≫ ParameterEquivalence.hilbertParameterEquiv n P F).left) =
      F.pullback f.left :=
    ((ParameterScheme.hilbertUniversalFamily S n P).pullback_comp (ParameterEquivalence.hilbertParameterEquiv n P F).left f.left).symm.trans
      (congrArg (fun H => H.pullback f.left) (hilbertUniversalFamily_classifies F))
  exact (hilbertUniversalFamily_existsUnique (F.pullback f.left)).unique h
    (hilbertUniversalFamily_classifies (F.pullback f.left))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ParameterUniversality
