import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.WeightedPrincipalQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TotalTorCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedGeometricComponents
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ClosedComponents
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterSum

/-! # Geometric Principal Quotient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricPrincipalQuotient

noncomputable section

section

/-! A regular principal quotient of a native reduced support has
an Euler pairing computed on the fixed global intersection components.
The weights are the native local divisor weights on those components. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace IsLocalRing

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem regular (Z : Scheme) (A : IrreducibleCloseds Z) (x : Z) (hx : x ∈ (A : Set Z))
    (r : Z.presheaf.stalk x) (hr : Local.Principal.supportStalkMap Z A x hx r ≠ 0) :
    IsSMulRegular (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hx) r := by
  have h : IsSMulRegular
      ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hx))
      (Local.Principal.supportStalkMap Z A x hx r) := IsSMulRegular.of_ne_zero hr
  exact h

variable (Z : Scheme) [IsLocallyNoetherian Z]
  (A B : IrreducibleCloseds Z) (x : Z) [IsDomain (Z.presheaf.stalk x)]
  (hxA : x ∈ (A : Set Z)) (hxB : x ∈ (B : Set Z))
  (r : Z.presheaf.stalk x) (hr : Local.Principal.supportStalkMap Z A x hxA r ≠ 0)
  (hrm : r ∈ maximalIdeal (Z.presheaf.stalk x))
  (d : ℕ) [HasProjectiveDimensionLE (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) d]
  (hisolated : (Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA) ∩
    Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB)) ∩
    Module.support (Z.presheaf.stalk x) ((Z.presheaf.stalk x) ⧸ Ideal.span {r}) ⊆
      {closedPoint (Z.presheaf.stalk x)})

include hr hrm hisolated

theorem exists_sum : ∃ T : Finset (PrimeSpectrum (Z.presheaf.stalk x)),
    (∀ p ∈ T, r ∉ p.asIdeal ∧
      ∃ D : irreducibleComponents (IsolatedGeometricComponents.intersection Z A B),
        CycleClass.Thom.IntersectionGeometry.closedComponentSupport Z (IsolatedGeometricComponents.intersection Z A B) D =
          Stalk.DivisorSupport.primeClosure Z x p) ∧
    (∀ p, p ≠ closedPoint (Z.presheaf.stalk x) → p ∉ T →
      TotalTorCoefficient.coefficient Z A B (Z.fromSpecStalk x p) d = 0) ∧
    Tor.Euler.euler (Z.presheaf.stalk x)
      (.of _ (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA))) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) d =
        ∑ p ∈ T, TotalTorCoefficient.coefficient Z A B (Z.fromSpecStalk x p) d *
          ((Ring.ord ((Z.presheaf.stalk x) ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r)).toNat : ℚ) := by
  let R := Z.presheaf.stalk x
  let M := CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB
  let : Module.Finite R M := Local.TorFinite.localSupportModule_finite Z A x hxA
  let : Module.Finite R N := Local.TorFinite.localSupportModule_finite Z B x hxB
  have hr₀ : r ≠ 0 := fun h => hr (by rw [h, map_zero])
  obtain ⟨T, hT, hout, he⟩ := WeightedPrincipalQuotient.exists_sum R M N r hr₀ hrm
    (regular Z A x hxA r hr) d hisolated
  refine ⟨T, ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨(hT p hp).2.2, IsolatedGeometricComponents.exists_component Z A B x hxA hxB r hrm
      hisolated p (hT p hp).1.1 (hT p hp).1.2 (hT p hp).2.1⟩
  · intro p hpn hpT
    rw [TotalTorCoefficient.localization Z A B x hxA hxB p d]
    exact hout p hpn hpT
  · exact he.trans (Finset.sum_congr rfl (fun p _ => by
      rw [TotalTorCoefficient.localization Z A B x hxA hxB p d]
      rfl))

theorem global_sum [NoetherianSpace Z] :
    Tor.Euler.euler (Z.presheaf.stalk x)
      (.of _ (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA))) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) d =
      ∑ C ∈ ProjectionFormula.Finite.ClosedComponents.components Z (IsolatedGeometricComponents.intersection Z A B),
        TotalTorCoefficient.coefficient Z A B (CycleClass.Thom.IntersectionGeometry.supportPoint C) d *
          GlobalParameterSum.Weights.weight Z x r C := by
  let c := fun C => TotalTorCoefficient.coefficient Z A B (CycleClass.Thom.IntersectionGeometry.supportPoint C) d
  let F := ProjectionFormula.Finite.ClosedComponents.components Z (IsolatedGeometricComponents.intersection Z A B)
  obtain ⟨T, hT, hout, he⟩ := exists_sum Z A B x hxA hxB r hr hrm d hisolated
  have hglobal := GlobalParameterSum.reindex Z x r hrm c F T (by
    intro p hp
    exact ⟨(ProjectionFormula.Finite.ClosedComponents.mem_iff Z _ _).mpr (hT p hp).2, (hT p hp).1⟩) (by
    intro p hp hpT
    change TotalTorCoefficient.coefficient Z A B
      (CycleClass.Thom.IntersectionGeometry.supportPoint (Stalk.DivisorSupport.primeClosure Z x p)) d = 0
    rw [Stalk.DivisorSupport.primeClosure_point]
    exact hout p hp hpT)
  exact he.trans ((Finset.sum_congr rfl (fun p _ => by
    rw [show c (Stalk.DivisorSupport.primeClosure Z x p) =
        TotalTorCoefficient.coefficient Z A B (Z.fromSpecStalk x p) d from
      congrArg (fun y => TotalTorCoefficient.coefficient Z A B y d)
        (Stalk.DivisorSupport.primeClosure_point Z x p)])).trans hglobal)

end

/-! The component formula for every nonzero native principal parameter,
including units, with isolation stated on the actual quotient module. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace IsLocalRing

namespace All

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem unit_quotient (R : Type) [CommRing R] (M : ModuleCat R) (r : R) (hr : IsUnit r) :
    Subsingleton (QuotSMulTop r M) :=
  Module.annihilator_eq_top_iff.mp
    ((Module.annihilator R (QuotSMulTop r M)).eq_top_of_isUnit_mem
      (QuotSMulTop.mem_annihilator M r) hr)

theorem unit_weight (Z : Scheme) (x : Z) (r : Z.presheaf.stalk x) (hr : IsUnit r)
    (C : IrreducibleCloseds Z) : GlobalParameterSum.Weights.weight Z x r C = 0 := by
  classical
  by_cases hx : x ∈ (C : Set Z)
  · have hu := hr.map (Local.Principal.supportStalkMap Z C x hx).hom
    simp only [GlobalParameterSum.Weights.weight, dite_eq_left hx, ite_eq_left hu.ne_zero,
      Ring.ord_of_isUnit hu, ENat.toNat_zero, Nat.cast_zero]
  · exact dite_eq_right hx

theorem coefficient (Z : Scheme) [IsLocallyNoetherian Z] [NoetherianSpace Z]
    (A B : IrreducibleCloseds Z) (x : Z) [IsDomain (Z.presheaf.stalk x)]
    (hxA : x ∈ (A : Set Z)) (hxB : x ∈ (B : Set Z))
    (r : Z.presheaf.stalk x) (hr : Local.Principal.supportStalkMap Z A x hxA r ≠ 0)
    (d : ℕ) [HasProjectiveDimensionLE (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) d]
    (hisolated : Module.support (Z.presheaf.stalk x) (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA)) ∩
      Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) ⊆
        {closedPoint (Z.presheaf.stalk x)}) :
    Tor.Euler.euler (Z.presheaf.stalk x)
      (.of _ (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA))) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) d =
      ∑ C ∈ ProjectionFormula.Finite.ClosedComponents.components Z (IsolatedGeometricComponents.intersection Z A B),
        TotalTorCoefficient.coefficient Z A B (CycleClass.Thom.IntersectionGeometry.supportPoint C) d *
          GlobalParameterSum.Weights.weight Z x r C := by
  classical
  by_cases hrm : r ∈ maximalIdeal (Z.presheaf.stalk x)
  · apply global_sum Z A B x hxA hxB r hr hrm d
    let : Module.Finite (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA) :=
      Local.TorFinite.localSupportModule_finite Z A x hxA
    intro p hp
    apply hisolated
    refine ⟨?_, hp.1.2⟩
    rw [Module.support_quotSMulTop]
    refine ⟨hp.1.1, ?_⟩
    have h := hp.2
    rw [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] at h
    exact Set.singleton_subset_iff.mpr (h (Ideal.subset_span (Set.mem_singleton r)))
  · have hu := notMem_maximalIdeal.mp hrm
    let : Subsingleton (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA)) :=
      unit_quotient (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA) r hu
    rw [PrimeFiltrationEuler.euler_zero_left]
    symm
    apply Finset.sum_eq_zero
    intro C _
    rw [unit_weight Z x r hu C, mul_zero]

end All

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricPrincipalQuotient
