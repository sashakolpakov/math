import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.ThickeningTopology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Functor

/-! # Topology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Topology.CrystallineFrameTopology

noncomputable section

/-!
# The topology of the native frame projection

A crystalline morphism inducing an isomorphism on residue rings is a
homeomorphism on ambient spectra. In particular the native frame
projection does not alter the ambient topological space.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]

theorem ambient_isHomeomorph_of_reduced_bijective
    (X : Over (Spec (CommRingCat.of k))) {P Q : Site.Object p k X}
    (f : P ⟶ Q) (hf : Function.Bijective f.reducedMap) :
    IsHomeomorph (PrimeSpectrum.comap f.ambientMap.toRingHom) := by
  have he : P.thickening.reduction.comp f.ambientMap.toRingHom =
      f.reducedMap.toRingHom.comp Q.thickening.reduction := RingHom.ext f.reduction_comm
  have hc : PrimeSpectrum.comap f.ambientMap.toRingHom ∘ PrimeSpectrum.comap P.thickening.reduction =
      PrimeSpectrum.comap Q.thickening.reduction ∘ PrimeSpectrum.comap f.reducedMap.toRingHom := by
    rw [← PrimeSpectrum.comap_comp, ← PrimeSpectrum.comap_comp, he]
  have hh := (PD.ThickeningTopology.PDThickeningTopology.reduction_isHomeomorph p k Q.residueRing Q.thickening).comp
    (PrimeSpectrum.isHomeomorph_comap_of_bijective hf)
  exact PD.ThickeningTopology.PDThickeningTopology.homeomorph_of_comp_right _ _
    (PD.ThickeningTopology.PDThickeningTopology.reduction_isHomeomorph p k P.residueRing P.thickening) (hc.symm ▸ hh)

variable (B σ : Type u) [CommRing B] [Algebra k B] (a : σ → B)

theorem projection_isHomeomorph
    (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) :
    IsHomeomorph (PrimeSpectrum.comap ((Functor.CrystallineFrameFunctor.projection p k B σ a).app Q).ambientMap.toRingHom) :=
  ambient_isHomeomorph_of_reduced_bijective p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)
    ((Functor.CrystallineFrameFunctor.projection p k B σ a).app Q) Function.bijective_id

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Topology.CrystallineFrameTopology
