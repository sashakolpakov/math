import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Stalk Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.StalkSupport

noncomputable section

/-! The defining prime of a reduced support stalk is preserved by an
open immersion whenever the actual generic support points correspond. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

theorem kernelPrime_comap {Y X : Scheme} (i : Y ⟶ X)
    (A : IrreducibleCloseds Y) (B : IrreducibleCloseds X)
    (hAB : i (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint B)
    (y : Y) (hy : y ∈ (A : Set Y)) (hx : i y ∈ (B : Set X)) :
    (Stalk.PrimeQuotient.kernelPrime Y A y hy).asIdeal.comap (i.stalkMap y).hom =
      (Stalk.PrimeQuotient.kernelPrime X B (i y) hx).asIdeal := by
  have he := congrArg (fun f : Spec (Y.presheaf.stalk y) ⟶ X => f (Stalk.PrimeQuotient.kernelPrime Y A y hy))
    (Scheme.SpecMap_stalkMap_fromSpecStalk i (x := y))
  change X.fromSpecStalk (i y) ((Spec.map (i.stalkMap y)) (Stalk.PrimeQuotient.kernelPrime Y A y hy)) =
    i (Y.fromSpecStalk y (Stalk.PrimeQuotient.kernelPrime Y A y hy)) at he
  rw [Stalk.PrimeQuotient.kernelPrime_image, hAB] at he
  have hp : (Spec.map (i.stalkMap y)) (Stalk.PrimeQuotient.kernelPrime Y A y hy) = Stalk.PrimeQuotient.kernelPrime X B (i y) hx :=
    (X.fromSpecStalk (i y)).isEmbedding.injective (he.trans (Stalk.PrimeQuotient.kernelPrime_image X B (i y) hx).symm)
  exact congrArg PrimeSpectrum.asIdeal hp

theorem kernelPrime_map {Y X : Scheme} (i : Y ⟶ X) [IsOpenImmersion i]
    (A : IrreducibleCloseds Y) (B : IrreducibleCloseds X)
    (hAB : i (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint B)
    (y : Y) (hy : y ∈ (A : Set Y)) (hx : i y ∈ (B : Set X)) :
    (Stalk.PrimeQuotient.kernelPrime X B (i y) hx).asIdeal.map (i.stalkMap y).hom =
      (Stalk.PrimeQuotient.kernelPrime Y A y hy).asIdeal := by
  rw [← kernelPrime_comap i A B hAB y hy hx]
  exact Ideal.map_comap_of_surjective _ (ConcreteCategory.bijective_of_isIso (i.stalkMap y)).surjective _

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.StalkSupport
