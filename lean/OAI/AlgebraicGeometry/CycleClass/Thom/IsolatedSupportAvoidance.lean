import OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerEmpty

/-! # Isolated Support Avoidance -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedSupportAvoidance.Constructions

noncomputable section

/-! At the generic point of a higher-codimension target, isolated
equations cannot vanish identically on an intermediate lower-codimension
parent. This directly supplies the prime-avoidance hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p d : ℕ) (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (C : Geometric.DimensionCycles.DimensionCycleSupport V d) (hp : p < d)
  (hxD : IntersectionGeometry.supportPoint C.val ∈ (D.val : Set V.carrier))
  (rs : List (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C.val)))

include hp

theorem ideal_not_le_supportKernel
    (hi : PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C.val))) ∩
      Module.support (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C.val))
        (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val (IntersectionGeometry.supportPoint C.val) hxD) ⊆
          {IsLocalRing.closedPoint (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C.val))}) :
    ¬ Ideal.ofList rs ≤ (StalkPrimeQuotient.Constructions.kernelPrime V.carrier D.val (IntersectionGeometry.supportPoint C.val) hxD).asIdeal := by
  intro hI
  let x := IntersectionGeometry.supportPoint C.val
  let P := StalkPrimeQuotient.Constructions.kernelPrime V.carrier D.val x hxD
  have hP : P ∈ Module.support (V.carrier.presheaf.stalk x) (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) := by
    apply Module.mem_support_iff_of_finite.mpr
    rw [Ideal.annihilator_quotient]
  have he := Set.mem_singleton_iff.mp (hi ⟨hI, hP⟩)
  have hg : IntersectionGeometry.supportPoint D.val = IntersectionGeometry.supportPoint C.val :=
    (StalkPrimeQuotient.Constructions.kernelPrime_image V.carrier D.val x hxD).symm.trans
      ((congrArg (V.carrier.fromSpecStalk x) he).trans Scheme.fromSpecStalk_closedPoint)
  have hDC : D.val = C.val := irreducibleSetEquivPoints.injective hg
  have hd := congrArg (Geometric.DimensionCycles.dimensionCodimension V) hDC
  rw [D.property, C.property] at hd
  exact (Nat.ne_of_lt hp) hd

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedSupportAvoidance.Constructions
