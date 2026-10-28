import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TripleExpansion
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.MultiplicitySum

/-! # Triple Coefficient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TripleCoefficient

noncomputable section

/-! The local triple Euler expansion is the coefficient pairing of the
actual intermediate proper-intersection cycle. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem reindex (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q t : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q) (D : X.DimensionCycleSupport t)
    (hpair : Supports.ProperCycle.pairMeetsProperly X p q A B) (C : X.DimensionCycleSupport (p + q + t))
    (F : Finset (PrimeSpectrum (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))))
    (hF : ∀ v ∈ F, X.supportCodimension (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) v) = p + q)
    (hout : ∀ v, X.supportCodimension (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) v) = p + q → v ∉ F →
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) v) = 0) :
    (Supports.ProperCycle.pairCycle X m p q A B).sum (fun E c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X E.val D.val C.val) =
      ∑ s ∈ F, CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) s) *
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) s) D.val C.val := by
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  let v (s : {s // s ∈ F}) : X.DimensionCycleSupport (p + q) :=
    ⟨Stalk.DivisorSupport.primeClosure X.carrier x s.val, hF s.val s.property⟩
  let w (s : {s // s ∈ F}) := CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val (Stalk.DivisorSupport.primeClosure X.carrier x s.val)
  let e (E : X.DimensionCycleSupport (p + q)) := CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X E.val D.val C.val
  have hv : Function.Injective v := by
    intro s s' h
    apply Subtype.ext
    apply (X.carrier.fromSpecStalk x).isEmbedding.injective
    rw [← Stalk.DivisorSupport.primeClosure_point X.carrier x s.val, ← Stalk.DivisorSupport.primeClosure_point X.carrier x s'.val]
    exact congrArg CycleClass.Thom.IntersectionGeometry.supportPoint (congrArg Subtype.val h)
  have hc (s : {s // s ∈ F}) (_hs : s ∈ (Finset.univ : Finset {s // s ∈ F})) :
      Supports.ProperCycle.pairCycle X m p q A B (v s) = w s := Supports.ProperCycle.pairCycle_apply X m p q A B hpair (v s)
  have ho (E : X.DimensionCycleSupport (p + q)) (hE : E ∉ Finset.univ.image v) :
      Supports.ProperCycle.pairCycle X m p q A B E * e E = 0 := by
    by_cases hxE : x ∈ (E.val : Set X.carrier)
    · have hr : CycleClass.Thom.IntersectionGeometry.supportPoint E.val ∈ Set.range (X.carrier.fromSpecStalk x) := by
        rw [Scheme.range_fromSpecStalk]
        exact (E.val.isIrreducible.isGenericPoint_genericPoint E.val.isClosed).specializes hxE
      obtain ⟨s, hs⟩ := hr
      have hsE : Stalk.DivisorSupport.primeClosure X.carrier x s = E.val := by
        apply irreducibleSetEquivPoints.injective
        exact (Stalk.DivisorSupport.primeClosure_point X.carrier x s).trans hs
      have hsF : s ∉ F := by
        intro hsF
        apply hE
        refine Finset.mem_image.mpr ⟨⟨s, hsF⟩, Finset.mem_univ _, ?_⟩
        apply Subtype.ext
        exact hsE
      have hz := hout s (by rw [hsE]; exact E.property) hsF
      rw [hsE] at hz
      rw [Supports.ProperCycle.pairCycle_apply X m p q A B hpair E, hz, zero_mul]
    · have hz : e E = 0 := dite_eq_right (fun h => hxE h.1)
      rw [hz, mul_zero]
  have h := Finite.MultiplicitySum.LocalCycle.reindex (Supports.ProperCycle.pairCycle X m p q A B) e Finset.univ v hv w hc ho
  calc
    _ = ∑ s : {s // s ∈ F}, w s * e (v s) := h
    _ = _ := by
      change (∑ s : {s // s ∈ F},
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val (Stalk.DivisorSupport.primeClosure X.carrier x s.val) *
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier x s.val) D.val C.val) = _
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach F (fun s =>
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val (Stalk.DivisorSupport.primeClosure X.carrier x s) *
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier x s) D.val C.val)

theorem euler_eq_pair_sum (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q t : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q) (D : X.DimensionCycleSupport t)
    (hpair : Supports.ProperCycle.pairMeetsProperly X p q A B)
    (htriple : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ ((A.val : Set X.carrier) ∩ B.val) ∩ D.val → p + q + t ≤ X.supportCodimension E)
    (C : X.DimensionCycleSupport (p + q + t))
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (hxB : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (B.val : Set X.carrier))
    (hxD : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (D.val : Set X.carrier)) :
    IteratedTorEuler.euler (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier D.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxD)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxB)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA) m m =
    (Supports.ProperCycle.pairCycle X m p q A B).sum (fun E c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X E.val D.val C.val) := by
  obtain ⟨F, hF, hout, he⟩ := TripleExpansion.exists_sum X m p q t A B D hpair htriple C hxA hxB hxD
  exact he.trans (reindex X m p q t A B D hpair C F (fun s hs => (hF s hs).1) hout).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TripleCoefficient
