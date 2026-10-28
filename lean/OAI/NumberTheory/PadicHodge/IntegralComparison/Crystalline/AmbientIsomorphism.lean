import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Isomorphisms

/-! # Ambient Isomorphism -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.AmbientIsomorphism

noncomputable section

/-! An ambient algebra isomorphism between actual crystalline objects
also identifies their reduced open subschemes and divided powers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) {P Q : AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X}
  (f : P ⟶ Q) (h : Function.Bijective f.ambientMap)

include h in
theorem reduced_bijective : Function.Bijective f.reducedMap :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Isomorphisms.CrystallineOpenIsomorphisms.bijective_of_open_surjective (CommRingCat.ofHom f.reducedMap.toRingHom)
    (AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Isomorphisms.CrystallineOpenIsomorphisms.reduced_surjective p k X f
      (PrimeSpectrum.isHomeomorph_comap_of_bijective h).surjective)

def iso : P ≅ Q :=
  AlgebraicGeometry.Crystalline.Cohomology.Isomorphisms.CrystallineIsomorphisms.iso p k X f h (reduced_bijective p k X f h)

theorem iso_hom : (iso p k X f h).hom = f := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.AmbientIsomorphism
