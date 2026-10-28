import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.RegularPrimeEquation
import OAI.AlgebraicGeometry.CycleClass.Thom.EqualCodimensionStalkPrimes

/-! # Support Regular Head -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportRegularHead.Constructions

noncomputable section

/-! Common regular head equations for finitely many actual integral
cycle supports of one codimension through a point. Incomparability is
proved from the geometric codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EqualCodimensionStalkPrimes.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) (x : X.carrier)
  {ι : Type} [Fintype ι] (D : ι → X.DimensionCycleSupport p)
  (hxD : ∀ i, x ∈ ((D i).val : Set X.carrier))
  (r : X.carrier.presheaf.stalk x) (rs : List (X.carrier.presheaf.stalk x))
  (hr : IsWeaklyRegular (X.carrier.presheaf.stalk x) (r :: rs))
  (hm : ∀ a ∈ r :: rs, a ∈ IsLocalRing.maximalIdeal (X.carrier.presheaf.stalk x))
  (hI : ∀ i, ¬ Ideal.ofList (r :: rs) ≤ RingHom.ker (SupportStalkModule.Constructions.supportStalkMap X.carrier (D i).val x (hxD i)).hom)

local notation "R" => X.carrier.presheaf.stalk x

include hr hm hI in
theorem exists_regular_head :
    ∃ t ∈ Ideal.ofList rs,
      Ideal.ofList ((r + t) :: rs) = Ideal.ofList (r :: rs) ∧
      IsWeaklyRegular R ((r + t) :: rs) ∧
      (∀ a ∈ (r + t) :: rs, a ∈ IsLocalRing.maximalIdeal R) ∧
      ∀ i, SupportStalkModule.Constructions.supportStalkMap X.carrier (D i).val x (hxD i) (r + t) ≠ 0 := by
  classical
  let P : ι → Ideal R := fun i => (StalkPrimeQuotient.Constructions.kernelPrime X.carrier (D i).val x (hxD i)).asIdeal
  let F : Finset (Ideal R) := Finset.univ.image P
  have hP : ∀ Q ∈ F, Q.IsPrime := by
    intro Q hQ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
    exact (StalkPrimeQuotient.Constructions.kernelPrime X.carrier (D i).val x (hxD i)).isPrime
  have hA : ∀ Q ∈ F, ∀ Q' ∈ F, Q ≤ Q' → Q = Q' := by
    intro Q hQ Q' hQ' hle
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hQ'
    exact EqualCodimensionStalkPrimes.Constructions.kernel_antichain X p (D i) (D j) x (hxD i) (hxD j) hle
  have hIF : ∀ Q ∈ F, ¬ Ideal.ofList (r :: rs) ≤ Q := by
    intro Q hQ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
    exact hI i
  obtain ⟨t, ht, he, hreg, hmax, hn⟩ :=
    RegularPrimeEquation.Constructions.exists_regular_head R F hP hA r rs hr hm hIF
  refine ⟨t, ht, he, hreg, hmax, ?_⟩
  intro i
  exact (hn (P i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).1

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportRegularHead.Constructions
