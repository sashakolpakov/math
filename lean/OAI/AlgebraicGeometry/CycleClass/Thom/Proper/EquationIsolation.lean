import OAI.AlgebraicGeometry.CycleClass.Thom.Proper.TorLength
import OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerIdeal

/-! # Equation Isolation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Proper.EquationIsolation.Constructions

noncomputable section

/-! Actual equations of one reduced support inherit the isolated local
intersection property from geometric proper intersection. Both modules
are the native original ambient-stalk quotients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem quotient_support_eq_local (X : Scheme) (A : IrreducibleCloseds X) (x : X) (hx : x ∈ (A : Set X)) :
    Module.support (X.presheaf.stalk x) (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X A x hx) =
      Module.support (X.presheaf.stalk x) (IntersectionGeometry.localSupportModule X A x hx) :=
  (StalkPrimeQuotient.Constructions.moduleEquiv X A x hx (StalkPrimeQuotient.Constructions.kernelPrime X A x hx) (StalkPrimeQuotient.Constructions.kernelPrime_image X A x hx)).support_eq.symm

theorem kernel_zeroLocus_eq_local_support (X : Scheme) (A : IrreducibleCloseds X) (x : X) (hx : x ∈ (A : Set X)) :
    PrimeSpectrum.zeroLocus ((StalkPrimeQuotient.Constructions.kernelPrime X A x hx).asIdeal : Set (X.presheaf.stalk x)) =
      Module.support (X.presheaf.stalk x) (IntersectionGeometry.localSupportModule X A x hx) := by
  rw [← quotient_support_eq_local]
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]

theorem equations_isolated (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (d : ℕ) (A B : IrreducibleCloseds V.carrier)
    (hproper : ∀ D : IrreducibleCloseds V.carrier,
      (D : Set V.carrier) ⊆ (A : Set V.carrier) ∩ (B : Set V.carrier) → d ≤ Geometric.DimensionCycles.dimensionCodimension V D)
    (C : Geometric.DimensionCycles.DimensionCycleSupport V d) (hxA : IntersectionGeometry.supportPoint C.val ∈ (A : Set V.carrier))
    (hxB : IntersectionGeometry.supportPoint C.val ∈ (B : Set V.carrier))
    (rs : List (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C.val)))
    (hI : Ideal.ofList rs = (StalkPrimeQuotient.Constructions.kernelPrime V.carrier A (IntersectionGeometry.supportPoint C.val) hxA).asIdeal) :
    PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C.val))) ∩
      Module.support (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C.val))
        (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier B (IntersectionGeometry.supportPoint C.val) hxB) ⊆
          {IsLocalRing.closedPoint (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C.val))} := by
  let C' : V.presentation.DimensionCycleSupport d := ⟨C.val,
    (Integral.ProductSupport.Constructions.integralPresentation_supportCodimension V C.val).trans C.property⟩
  have hp : ∀ D : IrreducibleCloseds V.carrier,
      (D : Set V.carrier) ⊆ (A : Set V.carrier) ∩ (B : Set V.carrier) → d ≤ V.presentation.supportCodimension D := by
    intro D hD
    rw [Integral.ProductSupport.Constructions.integralPresentation_supportCodimension]
    exact hproper D hD
  rw [hI, kernel_zeroLocus_eq_local_support, quotient_support_eq_local]
  exact TorLength.local_support_intersection_subset V.presentation d A B hp C' hxA hxB

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Proper.EquationIsolation.Constructions
