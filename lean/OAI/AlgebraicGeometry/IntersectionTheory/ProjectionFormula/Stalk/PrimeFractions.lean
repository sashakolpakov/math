import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrincipalPrimes
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.FractionIdentity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeOrder

/-! # Prime Fractions -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeFractions

noncomputable section

/-! Unit representations along all local components of a divisor give
a single fraction in the ambient stalk which restricts nontrivially to
every component. No normality assumption is used. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem notMem_of_image_ne_zero (X : Scheme) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x))
    (r : X.presheaf.stalk x)
    (hr : Local.Principal.supportStalkMap X (DivisorSupport.primeClosure X x p) x (DivisorSupport.point_mem_primeClosure X x p) r ≠ 0) :
    r ∉ p.asIdeal := by
  have hk := PrimeQuotient.kernel_eq X (DivisorSupport.primeClosure X x p) x
    (DivisorSupport.point_mem_primeClosure X x p) p (DivisorSupport.primeClosure_point X x p).symm
  intro h
  apply hr
  exact RingHom.mem_ker.mp (hk.symm ▸ h)

theorem exists_fraction (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (f : X.presheaf.stalk x) (hf : f ≠ 0) (g : X.functionField) (hg : g ≠ 0)
    (hunit : ∀ p : PrimeSpectrum (X.presheaf.stalk x), p.asIdeal.height = 1 → f ∈ p.asIdeal →
      ∃ u : X.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint (DivisorSupport.primeClosure X x p)), IsUnit u ∧
        algebraMap (X.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint (DivisorSupport.primeClosure X x p))) X.functionField u = g) :
    ∃ a b : X.presheaf.stalk x, a ≠ 0 ∧ b ≠ 0 ∧
      (∀ p : PrimeSpectrum (X.presheaf.stalk x), p.asIdeal.height = 1 → f ∈ p.asIdeal →
        a ∉ p.asIdeal ∧ b ∉ p.asIdeal) ∧
      g = algebraMap (X.presheaf.stalk x) X.functionField a /
        algebraMap (X.presheaf.stalk x) X.functionField b := by
  apply Finite.PrincipalPrimes.exists_fraction (X.presheaf.stalk x) X.functionField f hf g hg
  intro p hp hfp
  obtain ⟨u, hu, hug⟩ := hunit p hp hfp
  let W := DivisorSupport.primeClosure X x p
  have hz : CycleClass.Thom.IntersectionGeometry.supportPoint W ∈ (W : Set X) :=
    (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem
  obtain ⟨a, b, ha, hb, hab, _⟩ := Support.LocalFraction.exists_fraction X W hz x
    (DivisorSupport.point_mem_primeClosure X x p) u hu
  rw [hug] at hab
  exact ⟨a, b, notMem_of_image_ne_zero X x p a ha, notMem_of_image_ne_zero X x p b hb, hab⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeFractions
