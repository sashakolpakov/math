import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Contraction

/-! # Principal Intersections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.PrincipalIntersections.FinitePrincipalIntersections

noncomputable section

/-!
# The actual Čech intersections of a finite principal-open family

The categorical product used by the Čech nerve is the principal open
defined by the product of its coefficients.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry PrimeSpectrum

universe u v

variable (R : Type u) [CommRing R] {α : Type v} [Fintype α] (s : α → R)

theorem basicOpen_prod : basicOpen (∏ i, s i) = ⨅ i, basicOpen (s i) := by
  apply TopologicalSpace.Opens.ext
  ext x
  simp only [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter, SetLike.mem_coe,
    mem_basicOpen, Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and, not_exists]

theorem categoricalProduct :
    (∏ᶜ (fun i => (basicOpen (s i) : (Spec (CommRingCat.of R)).Opens))) =
      basicOpen (∏ i, s i) := by
  rw [basicOpen_prod]
  apply le_antisymm
  · exact le_iInf (fun i => leOfHom (Pi.π _ i))
  · exact leOfHom (Pi.lift (fun i => homOfLE (iInf_le _ i)))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.PrincipalIntersections.FinitePrincipalIntersections
