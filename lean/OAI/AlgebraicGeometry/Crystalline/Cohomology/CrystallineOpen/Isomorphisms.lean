import OAI.AlgebraicGeometry.Crystalline.Cohomology.Isomorphisms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.ThickeningTopology
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Isomorphisms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Isomorphisms.CrystallineOpenIsomorphisms

noncomputable section

/-!
# Surjective open immersions in the native crystalline category

The reduced scheme map of every native morphism is an open immersion.
Nilpotent reduction identifies its points with the ambient points. Thus
a native morphism whose ambient map is a surjective open immersion is
an isomorphism preserving all native crystalline data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) {P Q : Site.Object p k X} (f : P ⟶ Q)

instance reduced_openImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom f.reducedMap.toRingHom)) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.reducedMap.toRingHom) ≫ Q.immersion) :=
    f.over_X.symm ▸ P.openImmersion
  exact IsOpenImmersion.of_comp _ Q.immersion

theorem reduced_surjective
    (hf : Function.Surjective (PrimeSpectrum.comap f.ambientMap.toRingHom)) :
    Function.Surjective (PrimeSpectrum.comap f.reducedMap.toRingHom) := by
  have he : P.thickening.reduction.comp f.ambientMap.toRingHom =
      f.reducedMap.toRingHom.comp Q.thickening.reduction := RingHom.ext f.reduction_comm
  have hc : PrimeSpectrum.comap f.ambientMap.toRingHom ∘ PrimeSpectrum.comap P.thickening.reduction =
      PrimeSpectrum.comap Q.thickening.reduction ∘ PrimeSpectrum.comap f.reducedMap.toRingHom := by
    rw [← PrimeSpectrum.comap_comp, ← PrimeSpectrum.comap_comp, he]
  intro x
  obtain ⟨y, hy⟩ := hf (PrimeSpectrum.comap Q.thickening.reduction x)
  obtain ⟨z, hz⟩ := (PD.ThickeningTopology.PDThickeningTopology.reduction_isHomeomorph p k P.residueRing P.thickening).surjective y
  refine ⟨z, (PD.ThickeningTopology.PDThickeningTopology.reduction_isHomeomorph p k Q.residueRing Q.thickening).injective ?_⟩
  exact ((congrFun hc z).symm.trans (congrArg (PrimeSpectrum.comap f.ambientMap.toRingHom) hz)).trans hy

theorem bijective_of_open_surjective {R S : CommRingCat.{u}} (g : R ⟶ S)
    [IsOpenImmersion (Spec.map g)] (hg : Function.Surjective (PrimeSpectrum.comap g.hom)) :
    Function.Bijective g.hom := by
  have hi : IsIso (Spec.map g) := isIso_of_isOpenImmersion_of_opensRange_eq_top _
    (TopologicalSpace.Opens.ext (Set.range_eq_univ.mpr hg))
  exact isIso_SpecMap_iff.mp hi

def iso [IsOpenImmersion ((Site.ambient p k X).map f)]
    (hf : Function.Surjective (PrimeSpectrum.comap f.ambientMap.toRingHom)) : P ≅ Q := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.ambientMap.toRingHom)) :=
    inferInstanceAs (IsOpenImmersion ((Site.ambient p k X).map f))
  exact Isomorphisms.CrystallineIsomorphisms.iso p k X f
    (bijective_of_open_surjective (CommRingCat.ofHom f.ambientMap.toRingHom) hf)
    (bijective_of_open_surjective (CommRingCat.ofHom f.reducedMap.toRingHom)
      (reduced_surjective p k X f hf))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Isomorphisms.CrystallineOpenIsomorphisms
