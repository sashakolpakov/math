import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicPrincipalExpansion
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalIsolation

/-! # Covered Principal Expansion -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoveredPrincipalExpansion

noncomputable section

/-! Full geometric support covers discharge the isolation condition
in the native principal-quotient expansion. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk

def pairing (R : Type) [CommRing R] (v : PrimeSpectrum R) (r : R)
    (A₀ : IrreducibleCloseds (Spec (.of R))) (x : PrimeSpectrum R)
    (hxA : x ∈ (A₀ : Set (Spec (.of R)))) (hvx : v.asIdeal ≤ x.asIdeal) (d : ℕ) : ℚ :=
  Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
    (.of _ (QuotSMulTop (StructureSheaf.toStalk R x r)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) (Affine.SupportStalk.support R v) x (Affine.SupportStalk.mem R v x hvx))))
    (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) d

theorem coefficient (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    (R : Type) [CommRing R] [IsNoetherianRing R]
    (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (v : PrimeSpectrum R) (r : R) (F : Finset (PrimeSpectrum R)) (a : V.RationalDimensionCycle p)
    (he : Principal.AffineExpansion.Expansion V p q j v r F a)
    (S : Finset (IrreducibleCloseds V.carrier))
    (hS : ∀ B ∈ S, q ≤ V.supportCodimension B)
    (hcover : ∀ w ∈ Module.support R (QuotSMulTop r (R ⧸ v.asIdeal)),
      ∃ B ∈ S, j w ∈ (B : Set V.carrier))
    (A : V.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (A₀ : IrreducibleCloseds (Spec (.of R))) (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (hproper : ∀ B ∈ S, ∀ D : IrreducibleCloseds V.carrier,
      (D : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B : Set V.carrier) →
        p + V.supportCodimension B ≤ V.supportCodimension D)
    (C : V.DimensionCycleSupport (p + q)) (x : PrimeSpectrum R)
    (hx : j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val) (hxA : x ∈ (A₀ : Set (Spec (.of R))))
    (hvx : v.asIdeal ≤ x.asIdeal) :
    pairing R v r A₀ x hxA hvx m =
      ∑ z ∈ F, Affine.PrincipalWeight.weight R v r z *
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity V (Affine.FiltrationAvoidance.support j z) A.val C.val := by
  exact IntrinsicPrincipalExpansion.Intrinsic.coefficient V m p q R j v r F a he A hAa A₀ hA C x hx hxA hvx
    (Affine.PrincipalIsolation.isolated V m p q R j v r S hS hcover A A₀ hA hproper C x hx hxA hvx)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoveredPrincipalExpansion
