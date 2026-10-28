import OAI.AlgebraicGeometry.CycleClass.Thom.Local.Intersection
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.QuotientBaseChange

/-! # Reduced Local Intersection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ReducedLocalIntersection

noncomputable section

/-! A local complete intersection whose restricted equations generate
the actual maximal ideal has Serre multiplicity one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.Intersection.Constructions

theorem intersectionMultiplicity_eq_one (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B C : IrreducibleCloseds X.carrier)
    (hxA : IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier)) (hxB : IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier))
    (rs : List (X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C)))
    (hA : RingHom.ker (SupportStalkModule.Constructions.supportStalkMap X.carrier A (IntersectionGeometry.supportPoint C) hxA).hom = Ideal.ofList rs)
    (hr : IsWeaklyRegular (X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C)) rs)
    (hB : IsWeaklyRegular (IntersectionGeometry.localSupportModule X.carrier B (IntersectionGeometry.supportPoint C) hxB) rs)
    (hmax : (Ideal.ofList rs).map (SupportStalkModule.Constructions.supportStalkMap X.carrier B (IntersectionGeometry.supportPoint C) hxB).hom =
      IsLocalRing.maximalIdeal ((Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk
        (IntersectionGeometry.supportPreimage B (IntersectionGeometry.supportPoint C) hxB))) : IntersectionGeometry.intersectionMultiplicity X A B C = 1 := by
  let R := X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C)
  let S := (Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk (IntersectionGeometry.supportPreimage B (IntersectionGeometry.supportPoint C) hxB)
  let σ := SupportStalkModule.Constructions.supportStalkMap X.carrier B (IntersectionGeometry.supportPoint C) hxB
  let : Algebra R S := σ.hom.toAlgebra
  have hσ : Function.Surjective (algebraMap R S) := SupportStalkModule.Constructions.supportStalkMap_surjective X.carrier B _ hxB
  have hm : (Ideal.ofList rs).map (algebraMap R S) = IsLocalRing.maximalIdeal S := hmax
  have hl : Module.length R (S ⧸ (Ideal.ofList rs • ⊤ : Submodule R S)) = 1 := by
    rw [Ideal.smul_top_eq_map, hm]
    change Module.length R (S ⧸ IsLocalRing.maximalIdeal S) = 1
    rw [Module.length_eq_of_surjective (M := S ⧸ IsLocalRing.maximalIdeal S) hσ]
    exact TorAlgebra.QuotientBaseChange.Tor.residue_quotient_length S
  rw [Local.Intersection.Constructions.intersectionMultiplicity_eq_quotientLength X A B C hxA hxB rs hA hr hB]
  change (Module.length R (S ⧸ (Ideal.ofList rs • ⊤ : Submodule R S))).toNat = (1 : ℚ)
  rw [hl]
  norm_num

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ReducedLocalIntersection
