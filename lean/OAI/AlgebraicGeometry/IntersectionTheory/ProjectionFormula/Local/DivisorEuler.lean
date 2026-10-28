import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfacePrimeEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.Stalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrincipalLeft
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDimension

/-! # Divisor Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.DivisorEuler

noncomputable section

/-! At an actual codimension-two point on a divisor, the order of a
nonzero local equation is the sum of the height-one contributions in a
prime filtration of its principal quotient. All finiteness, dimension,
torsion and projective-dimension inputs follow from the smooth presentation. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem order_eq_prime_sum (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport 1) (C : X.DimensionCycleSupport 2)
    (hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (r : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
    (hra : Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx r ≠ 0) :
    let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    let N := CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
    ∃ (n : ℕ) (primes : Fin n → PrimeSpectrum R),
      (∀ i, Module.support R (R ⧸ (primes i).asIdeal) ⊆ Module.support R (QuotSMulTop r R)) ∧
      (Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk
          (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx))
        (Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx r)).toNat =
        ∑ i ∈ Finset.univ.filter (fun i => (primes i).asIdeal.height = 1),
          Tor.Euler.euler R (.of R (R ⧸ (primes i).asIdeal)) N m := by
  let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
  let S := (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx)
  let σ := Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
  let : Algebra R S := σ.hom.toAlgebra
  let : IsDomain R := X.stalk_isDomain (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
  let : Module.Finite R N := TorFinite.localSupportModule_finite _ _ _ _
  let : HasProjectiveDimensionLE N m :=
    Smooth.StalkDimension.stalk_bound X.structureMap m (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) N
  have hCA : C.val ≤ A.val :=
    (Supports.supportPoint_mem_iff_subset
      (⟨(A.val : Set X.carrier), A.val.isClosed⟩ : Closeds X.carrier) C.val).mp hx
  have hdim : (IsLocalRing.maximalIdeal R).height = 2 :=
    Divisor.Stalk.maximalIdeal_height_two X m A C hCA
  have hker : RingHom.ker (algebraMap R S) ≠ ⊥ :=
    Divisor.Stalk.supportStalkMap_ker_ne_bot X m 1 (by decide) A _ hx
  have hσ : Function.Surjective (algebraMap R S) := Principal.supportStalkMap_surjective X.carrier A.val _ hx
  have hr : r ≠ 0 := by
    intro h
    apply hra
    rw [h, map_zero]
  have hr' : IsSMulRegular R r := fun _ _ h => mul_left_cancel₀ hr h
  have hisolated : Module.support R (QuotSMulTop r R) ∩ Module.support R N ⊆
      {IsLocalRing.closedPoint R} :=
    SurfacePrimeEuler.isolated_principal_support R hdim S hker r hra
  obtain ⟨n, primes, hsupp, he⟩ := SurfacePrimeEuler.exists_height_one_sum R hdim r hr N m
    (Divisor.Stalk.localSupport_torsion X m 1 (by decide) A _ hx) hisolated
  have horder : Tor.Euler.euler R (.of R (QuotSMulTop r R)) N m =
      (Ring.ord S (σ r)).toNat :=
    PrincipalLeft.euler_eq_order R S hσ r hr' hra (.of R (QuotSMulTop r R))
      (LinearEquiv.refl R _) m
  exact ⟨n, primes, hsupp, horder.symm.trans he⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.DivisorEuler
