import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoheightOneCodimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Through Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ThroughSupport

noncomputable section

/-! Every positive-codimension support in a smooth projective
presentation is contained in an actual divisor. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem exists_divisor (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (hp : 0 < p) (C : X.DimensionCycleSupport p) :
    ∃ A : X.DimensionCycleSupport 1, C.val ≤ A.val := by
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  let R := X.carrier.presheaf.stalk x
  let : IsDomain R := X.stalk_isDomain x
  have hx : x ∈ (C.val : Set X.carrier) :=
    (C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed).mem
  let q := Stalk.PrimeQuotient.kernelPrime X.carrier C.val x hx
  have hq0 : q.asIdeal ≠ ⊥ :=
    Stalk.supportStalkMap_ker_ne_bot X m p hp C x hx
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
  have hrm : r ∈ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal q.isPrime.ne_top hr
  obtain ⟨P, hP, _⟩ := Ideal.exists_minimalPrimes_le
    (show Ideal.span {r} ≤ IsLocalRing.maximalIdeal R from
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrm))
  have hrP : r ∈ P := hP.le (Ideal.subset_span (Set.mem_singleton r))
  have hP0 : P ≠ ⊥ := by
    intro he
    exact hr0 (by simpa only [he, Submodule.mem_bot] using hrP)
  have hheight : P.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {r}) P hP)
    (Order.one_le_iff_ne_zero.mpr (mt Ideal.height_eq_zero_iff_eq_bot.mp hP0))
  let z : Spec R := ⟨P, hP.isPrime⟩
  let W := Stalk.DivisorSupport.primeClosure X.carrier x z
  have hW : X.supportCodimension W = 1 := by
    apply CoheightOneCodimension.codimension X m W
    rw [Stalk.DivisorSupport.primeClosure_point, ← Stalk.Localization.height_eq_coheight_image]
    exact hheight
  refine ⟨⟨W, hW⟩, ?_⟩
  change (C.val : Set X.carrier) ⊆ (W : Set X.carrier)
  apply (Supports.supportPoint_mem_iff_subset
    (⟨W, W.isClosed⟩ : Closeds X.carrier) C.val).mp
  exact Stalk.DivisorSupport.point_mem_primeClosure X.carrier x z

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ThroughSupport
