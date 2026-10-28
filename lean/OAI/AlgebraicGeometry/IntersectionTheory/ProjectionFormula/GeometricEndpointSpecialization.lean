import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TotalTorCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EndpointTorComparison
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.WeightedSpecialization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.AffineParameter
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedGeometricComponents

/-! # Geometric Endpoint Specialization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricEndpointSpecialization

noncomputable section

/-! An isolated native endpoint intersection is the finite weighted
sum of native family coefficients on actual global intersection
components. Endpoint Tor is transported through the actual quotient map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace IsLocalRing
open scoped _root_.Polynomial

variable (Z : Scheme) [IsIntegral Z] [IsLocallyNoetherian Z]
  (t : Z ⟶ Spec (.of ℂ[X])) [Flat t] (A B : IrreducibleCloseds Z)
  [Flat (CycleClass.Geometric.GenericPoint.reducedSupportι A ≫ t)] [Flat (CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ t)]
  (x : Z) (hxA : x ∈ (A : Set Z)) (hxB : x ∈ (B : Set Z))
  (a : ℂ) (hx : t x = Affine.ParameterFiber.point ℂ a)
  (S : Type) [CommRing S] (φ : Z.presheaf.stalk x →+* S) (hφ : Function.Surjective φ)
  (hk : RingHom.ker φ = Ideal.span {Affine.ParameterFiber.germ ℂ t x a})
  (M₀ N₀ : ModuleCat S)
  (eM : QuotSMulTop (Affine.ParameterFiber.germ ℂ t x a) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA) ≃ₗ[
    Z.presheaf.stalk x] (ModuleCat.restrictScalars φ).obj M₀)
  (eN : QuotSMulTop (Affine.ParameterFiber.germ ℂ t x a) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) ≃ₗ[
    Z.presheaf.stalk x] (ModuleCat.restrictScalars φ).obj N₀)
  (d : ℕ) [HasProjectiveDimensionLE (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) d]
  (hisolated : (Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA) ∩
    Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB)) ∩
    Module.support (Z.presheaf.stalk x)
      ((Z.presheaf.stalk x) ⧸ Ideal.span {Affine.ParameterFiber.germ ℂ t x a}) ⊆
      {closedPoint (Z.presheaf.stalk x)})

include hx hφ hk eM eN hisolated

theorem exists_sum : ∃ T : Finset (PrimeSpectrum (Z.presheaf.stalk x)),
    (∀ p ∈ T, Affine.ParameterFiber.germ ℂ t x a ∉ p.asIdeal ∧
      ∃ D : irreducibleComponents (IsolatedGeometricComponents.intersection Z A B),
        CycleClass.Thom.IntersectionGeometry.closedComponentSupport Z (IsolatedGeometricComponents.intersection Z A B) D =
          Stalk.DivisorSupport.primeClosure Z x p) ∧
    (∀ p, p ≠ closedPoint (Z.presheaf.stalk x) → p ∉ T →
      TotalTorCoefficient.coefficient Z A B (Z.fromSpecStalk x p) d = 0) ∧
    Tor.Euler.euler S M₀ N₀ d =
      ∑ p ∈ T, TotalTorCoefficient.coefficient Z A B (Z.fromSpecStalk x p) d *
        ((Ring.ord ((Z.presheaf.stalk x) ⧸ p.asIdeal)
          (Ideal.Quotient.mk p.asIdeal (Affine.ParameterFiber.germ ℂ t x a))).toNat : ℚ) := by
  let R := Z.presheaf.stalk x
  let M := CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB
  let r : R := Affine.ParameterFiber.germ ℂ t x a
  let : Module.Finite R M := Local.TorFinite.localSupportModule_finite Z A x hxA
  let : Module.Finite R N := Local.TorFinite.localSupportModule_finite Z B x hxB
  have hr : r ≠ 0 := ProjectionFormula.Flat.AffineParameter.nonzero ℂ t x a
  have hrm : r ∈ maximalIdeal R := (Affine.ParameterFiber.germ_mem_maximalIdeal ℂ t x a).mpr hx
  have hM := ProjectionFormula.Flat.AffineParameter.support_regular Z A t x hxA a
  have hN := ProjectionFormula.Flat.AffineParameter.support_regular Z B t x hxB a
  obtain ⟨T, hT, hout, hsum⟩ :=
    Parameter.WeightedSpecialization.exists_sum R M N r hr hrm hM hN d hisolated
  refine ⟨T, ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨(hT p hp).2.2, IsolatedGeometricComponents.exists_component Z A B x hxA hxB r hrm
      hisolated p (hT p hp).1.1 (hT p hp).1.2 (hT p hp).2.1⟩
  · intro p hpn hpT
    rw [TotalTorCoefficient.localization Z A B x hxA hxB p d]
    exact hout p hpn hpT
  · calc
      _ = Tor.Euler.euler (Parameter.ScalarQuotient.Ring R r)
          ((Parameter.ScalarQuotient.quotient R r).obj M)
          ((Parameter.ScalarQuotient.quotient R r).obj N) d :=
        (EndpointTorComparison.euler R S r φ hφ hk M N M₀ N₀ eM eN d).symm
      _ = _ := hsum.trans (Finset.sum_congr rfl (fun p _ => by
        rw [TotalTorCoefficient.localization Z A B x hxA hxB p d]
        rfl))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricEndpointSpecialization
