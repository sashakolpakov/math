import OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Stalk Support -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport

/-! The defining prime of a reduced support stalk is preserved by an
open immersion whenever the actual generic support points correspond. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions

theorem kernelPrime_comap {Y X : Scheme} (i : Y ⟶ X)
    (A : IrreducibleCloseds Y) (B : IrreducibleCloseds X)
    (hAB : i (IntersectionGeometry.supportPoint A) = IntersectionGeometry.supportPoint B)
    (y : Y) (hy : y ∈ (A : Set Y)) (hx : i y ∈ (B : Set X)) :
    (StalkPrimeQuotient.Constructions.kernelPrime Y A y hy).asIdeal.comap (i.stalkMap y).hom =
      (StalkPrimeQuotient.Constructions.kernelPrime X B (i y) hx).asIdeal := by
  have he := congrArg (fun f : Spec (Y.presheaf.stalk y) ⟶ X => f (StalkPrimeQuotient.Constructions.kernelPrime Y A y hy))
    (Scheme.SpecMap_stalkMap_fromSpecStalk i (x := y))
  change X.fromSpecStalk (i y) ((Spec.map (i.stalkMap y)) (StalkPrimeQuotient.Constructions.kernelPrime Y A y hy)) =
    i (Y.fromSpecStalk y (StalkPrimeQuotient.Constructions.kernelPrime Y A y hy)) at he
  rw [StalkPrimeQuotient.Constructions.kernelPrime_image, hAB] at he
  have hp : (Spec.map (i.stalkMap y)) (StalkPrimeQuotient.Constructions.kernelPrime Y A y hy) = StalkPrimeQuotient.Constructions.kernelPrime X B (i y) hx :=
    (X.fromSpecStalk (i y)).isEmbedding.injective (he.trans (StalkPrimeQuotient.Constructions.kernelPrime_image X B (i y) hx).symm)
  exact congrArg PrimeSpectrum.asIdeal hp

theorem kernelPrime_map {Y X : Scheme} (i : Y ⟶ X) [IsOpenImmersion i]
    (A : IrreducibleCloseds Y) (B : IrreducibleCloseds X)
    (hAB : i (IntersectionGeometry.supportPoint A) = IntersectionGeometry.supportPoint B)
    (y : Y) (hy : y ∈ (A : Set Y)) (hx : i y ∈ (B : Set X)) :
    (StalkPrimeQuotient.Constructions.kernelPrime X B (i y) hx).asIdeal.map (i.stalkMap y).hom =
      (StalkPrimeQuotient.Constructions.kernelPrime Y A y hy).asIdeal := by
  rw [← kernelPrime_comap i A B hAB y hy hx]
  exact Ideal.map_comap_of_surjective _ (ConcreteCategory.bijective_of_isIso (i.stalkMap y)).surjective _

end Constructions

end AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport

namespace AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport.Constructions.Restriction

/-! A reduced irreducible support meeting an open immersion restricts
to its genuine irreducible inverse image. Its generic point and native
stalk ideal commute with the original open immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] (A : IrreducibleCloseds Y)

theorem generic_mem_range (x : X) (hx : f x ∈ (A : Set Y)) : IntersectionGeometry.supportPoint A ∈ Set.range f := by
  have h := (A.isIrreducible.isGenericPoint_genericPoint A.isClosed).specializes hx
  exact h.mem_open f.isOpenEmbedding.isOpen_range ⟨x, rfl⟩

variable (hA : IntersectionGeometry.supportPoint A ∈ Set.range f)

def restrictedSupport : IrreducibleCloseds X := irreducibleSetEquivPoints.symm hA.choose

omit [IsOpenImmersion f] in
theorem restrictedSupport_genericPoint : f (IntersectionGeometry.supportPoint (restrictedSupport f A hA)) = IntersectionGeometry.supportPoint A := by
  change f (irreducibleSetEquivPoints (irreducibleSetEquivPoints.symm hA.choose)) = IntersectionGeometry.supportPoint A
  rw [OrderIso.apply_symm_apply]
  exact hA.choose_spec

theorem restrictedSupport_coe : (restrictedSupport f A hA : Set X) = f ⁻¹' (A : Set Y) := by
  have h := f.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image ({hA.choose} : Set X)
  rw [Set.image_singleton, hA.choose_spec] at h
  exact h.trans (congrArg (fun S : Set Y => f ⁻¹' S)
    (A.isIrreducible.isGenericPoint_genericPoint A.isClosed))

theorem restrictedSupport_mem (x : X) (hx : f x ∈ (A : Set Y)) : x ∈ (restrictedSupport f A hA : Set X) := by
  rw [restrictedSupport_coe]
  exact hx

theorem restrictedSupport_kernel (x : X) (hx : f x ∈ (A : Set Y)) :
    (StalkPrimeQuotient.Constructions.kernelPrime Y A (f x) hx).asIdeal.map (f.stalkMap x).hom =
      (StalkPrimeQuotient.Constructions.kernelPrime X (restrictedSupport f A hA) x (restrictedSupport_mem f A hA x hx)).asIdeal :=
  kernelPrime_map f (restrictedSupport f A hA) A (restrictedSupport_genericPoint f A hA) x
    (restrictedSupport_mem f A hA x hx) hx

end AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport.Constructions.Restriction

end

end OAI
