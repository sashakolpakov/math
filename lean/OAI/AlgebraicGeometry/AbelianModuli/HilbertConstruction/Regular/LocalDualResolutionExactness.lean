import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.DualFirstRelations

/-! # Local Dual Resolution Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.LocalDualResolutionExactness

noncomputable section

/-! The full nonnegative chain dual of a dimension-bounded finite free complex supported at the closed point is exact in every positive degree. Only its degree-zero augmentation remains to identify a projective resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

theorem regularLocal_dualComplex_exact_positive
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (hbound : ∀ q, g < q → IsZero (C.X q))
    (rs : List R) (hlen : rs.length = g) (hreg : SequenceBasic.RingTheory.Sequence.IsRegular R rs)
    (hgen : SequenceBasic.Ideal.ofList rs = maximalIdeal R)
    (hfield : Cochain.FieldSupport.CochainFieldSupport C (maximalIdeal R)) :
    ∀ q, 0 < q → (HilbertConstruction.Module.DualFunctor.dualModuleComplex C).ExactAt q := by
  let K : ChainComplex (ModuleCat.{u} R) ℕ := HilbertConstruction.Module.DualFunctor.dualModuleComplex C
  let : K.IsStrictlySupported (Bounded.DualCochain.finiteDualEmbedding g) := {
    isZero := fun q hq => by
      have hz := hbound q ((Bounded.DualCochain.finiteDualEmbedding_outside_iff g q).mp hq)
      have : Subsingleton (C.X q) := ModuleCat.subsingleton_of_isZero hz
      change IsZero (ModuleCat.of R (Module.Dual R (C.X q)))
      exact ModuleCat.isZero_of_subsingleton _ }
  intro q hq
  change K.ExactAt q
  by_cases hqg : q ≤ g
  · let j : Fin (g + 1) := ⟨g - q, by omega⟩
    have hj : (Bounded.DualCochain.finiteDualEmbedding g).f j = q := by
      change j.rev.val = q
      rw [Fin.val_rev]
      change g + 1 - (g - q + 1) = q
      omega
    have hz := Bounded.DualFirstRelations.regularLocal_boundedDual_homology_zero_below C g hfin hfree hbound
      rs hlen hreg hgen hfield (g - q) (by omega)
    have he : (Bounded.DualCochain.boundedDualCochain C g).ExactAt (g - q) :=
      ((Bounded.DualCochain.boundedDualCochain C g).exactAt_iff_isZero_homology _).mpr hz
    have hr : (Bounded.DualCochain.finiteDualCochain C g).ExactAt j :=
      ((Bounded.DualCochain.finiteDualCochain C g).extend_exactAt_iff (HilbertConstruction.Finite.CochainTruncation.finiteCochainEmbedding g)
        (j := j) (j' := g - q) rfl).mp he
    have he' := (Additive.ComplexExtension.supported_restriction_exactAt_iff (Bounded.DualCochain.finiteDualEmbedding g) K j).mp hr
    simpa only [hj] using he'
  · exact HomologicalComplex.ExactAt.of_isZero
      (K.isZero_X_of_isStrictlySupported (Bounded.DualCochain.finiteDualEmbedding g) q
        ((Bounded.DualCochain.finiteDualEmbedding_outside_iff g q).mpr (Nat.lt_of_not_ge hqg)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.LocalDualResolutionExactness
