import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.DualFieldSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.LocalCochainAcyclicity

/-! # Dual First Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.DualFirstRelations

noncomputable section

/-! Over a regular local ring, a bounded finite free complex supported at the closed point has an exact reversed dual at its first relation module. This includes dimension one, where an endpoint outside the interval is zero. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

theorem regularLocal_boundedDual_homology_zero_below
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (hbound : ∀ q, g < q → IsZero (C.X q))
    (rs : List R) (hlen : rs.length = g) (hreg : Regular.SequenceBasic.RingTheory.Sequence.IsRegular R rs)
    (hgen : Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal R)
    (hfield : Cochain.FieldSupport.CochainFieldSupport C (maximalIdeal R)) :
    ∀ q, q < g → IsZero ((DualCochain.boundedDualCochain C g).homology q) := by
  have hff := DualCochain.boundedDualCochain_finite_free C g hfin hfree
  exact Regular.LocalCochainAcyclicity.regularLocalCochain_homology_zero_below_regular_parameters g R
    (DualCochain.boundedDualCochain C g) (fun q => (hff q).1) (fun q => (hff q).2)
    rs hlen hreg hgen (DualFieldSupport.boundedDualCochain_fieldSupport C g hfin hfree hbound _ hfield)

theorem regularLocal_firstDualRelations_exact
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ) (hg : 0 < g)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (hbound : ∀ q, g < q → IsZero (C.X q))
    (rs : List R) (hlen : rs.length = g) (hreg : Regular.SequenceBasic.RingTheory.Sequence.IsRegular R rs)
    (hgen : Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal R)
    (hfield : Cochain.FieldSupport.CochainFieldSupport C (maximalIdeal R)) :
    (HilbertConstruction.Module.DualFunctor.dualModuleShortComplex (C.sc' 0 1 2)).Exact := by
  let j : Fin (g + 1) := ⟨g - 1, by omega⟩
  have hj : (DualCochain.finiteDualEmbedding g).f j = 1 := by
    change j.rev.val = 1
    rw [Fin.val_rev]
    change g + 1 - (g - 1 + 1) = 1
    omega
  have hz := regularLocal_boundedDual_homology_zero_below C g hfin hfree hbound
    rs hlen hreg hgen hfield (g - 1) (by omega)
  have he : (DualCochain.boundedDualCochain C g).ExactAt (g - 1) :=
    ((DualCochain.boundedDualCochain C g).exactAt_iff_isZero_homology _).mpr hz
  have hr : (DualCochain.finiteDualCochain C g).ExactAt j :=
    ((DualCochain.finiteDualCochain C g).extend_exactAt_iff (HilbertConstruction.Finite.CochainTruncation.finiteCochainEmbedding g)
      (j := j) (j' := g - 1) rfl).mp he
  let K : ChainComplex (ModuleCat.{u} R) ℕ := HilbertConstruction.Module.DualFunctor.dualModuleComplex C
  let : K.IsStrictlySupported (DualCochain.finiteDualEmbedding g) := {
    isZero := fun q hq => by
      have hzq := hbound q ((DualCochain.finiteDualEmbedding_outside_iff g q).mp hq)
      have : Subsingleton (C.X q) := ModuleCat.subsingleton_of_isZero hzq
      change IsZero (ModuleCat.of R (Module.Dual R (C.X q)))
      exact ModuleCat.isZero_of_subsingleton _ }
  have heK : K.ExactAt 1 := by
    have he' := (Additive.ComplexExtension.supported_restriction_exactAt_iff (DualCochain.finiteDualEmbedding g) K j).mp hr
    simpa only [hj] using he'
  exact (K.exactAt_iff' 2 1 0 (by simp) (by simp)).mp heK

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.DualFirstRelations
