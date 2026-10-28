import OAI.AlgebraicGeometry.CycleClass.Thom.Tor.RegularSequence
import OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule

/-! # Intersection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.Intersection

noncomputable section

/-! If one reduced support is cut out locally by a sequence regular both
on the ambient ring and on the other support, its Serre coefficient is
the length of the actual restricted quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions

theorem intersectionMultiplicity_eq_quotientLength (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B C : IrreducibleCloseds X.carrier)
    (hxA : IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier)) (hxB : IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier))
    (rs : List (X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C)))
    (hA : RingHom.ker (SupportStalkModule.Constructions.supportStalkMap X.carrier A (IntersectionGeometry.supportPoint C) hxA).hom = Ideal.ofList rs)
    (hr : IsWeaklyRegular (X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C)) rs)
    (hB : IsWeaklyRegular (IntersectionGeometry.localSupportModule X.carrier B (IntersectionGeometry.supportPoint C) hxB) rs) :
    IntersectionGeometry.intersectionMultiplicity X A B C =
      (Module.length (X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C))
        ((IntersectionGeometry.localSupportModule X.carrier B (IntersectionGeometry.supportPoint C) hxB) ⧸
          (Ideal.ofList rs • ⊤ : Submodule (X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C))
            (IntersectionGeometry.localSupportModule X.carrier B (IntersectionGeometry.supportPoint C) hxB)))).toNat := by
  let R := X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C)
  let T := (Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (IntersectionGeometry.supportPreimage A (IntersectionGeometry.supportPoint C) hxA)
  let σ := SupportStalkModule.Constructions.supportStalkMap X.carrier A (IntersectionGeometry.supportPoint C) hxA
  let : Algebra R T := σ.hom.toAlgebra
  have hσ : Function.Surjective (Algebra.ofId R T) := SupportStalkModule.Constructions.supportStalkMap_surjective X.carrier A _ hxA
  let e : IntersectionGeometry.localSupportModule X.carrier A (IntersectionGeometry.supportPoint C) hxA ≃ₗ[R] (R ⧸ Ideal.ofList rs) :=
    (Ideal.quotientKerAlgEquivOfSurjective hσ).symm.toLinearEquiv.trans
      (Submodule.quotEquivOfEq _ _ hA)
  let N := IntersectionGeometry.localSupportModule X.carrier B (IntersectionGeometry.supportPoint C) hxB
  have hlen (i : ℕ) : IntersectionGeometry.localTorLength X.carrier A B (IntersectionGeometry.supportPoint C) hxA hxB i =
      Module.length R (((Tor (ModuleCat R) i).obj (ModuleCat.of R (R ⧸ Ideal.ofList rs))).obj N) :=
    ((((Tor (ModuleCat R) i).mapIso e.toModuleIso).app N).toLinearEquiv).length_eq
  rw [IntersectionGeometry.intersectionMultiplicity, dite_eq_left ⟨hxA, hxB⟩]
  simp_rw [hlen]
  exact Thom.Tor.RegularSequence.Constructions.euler_regular_quotient_eq_length R N rs hr hB X.ambientDimension

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.Intersection
