import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk
import Mathlib.RingTheory.Localization.Algebra

/-! # Closed Stalk Kernel -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ClosedStalkKernel

noncomputable section

/-! For a surjective affine coordinate map, the kernel of its
actual scheme stalk map is the localized coordinate kernel. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
  (hf : Function.Surjective f) (q : Spec (.of S))

include hf

theorem kernel : RingHom.ker ((Spec.map (CommRingCat.ofHom f)).stalkMap q).hom =
    (RingHom.ker f).map (StructureSheaf.toStalk R (PrimeSpectrum.comap f q)).hom := by
  let p : Spec (.of R) := (Spec.map (CommRingCat.ofHom f)) q
  let Rp := (Spec (.of R)).presheaf.stalk p
  let Sq := (Spec (.of S)).presheaf.stalk q
  let : Algebra R Rp := (StructureSheaf.toStalk R p).hom.toAlgebra
  let : Algebra S Sq := (StructureSheaf.toStalk S q).hom.toAlgebra
  let : IsLocalization p.asIdeal.primeCompl Rp := by
    change IsLocalization p.asIdeal.primeCompl ((structurePresheafInCommRingCat R).stalk p)
    infer_instance
  let : IsLocalization q.asIdeal.primeCompl Sq := by
    change IsLocalization q.asIdeal.primeCompl ((structurePresheafInCommRingCat S).stalk q)
    infer_instance
  have hmap : p.asIdeal.primeCompl.map f = q.asIdeal.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective f hf q.asIdeal
  have he : ((Spec.map (CommRingCat.ofHom f)).stalkMap q).hom =
      (IsLocalization.map Sq f (hmap.symm ▸ p.asIdeal.primeCompl.le_comap_map) : Rp →+* Sq) := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    apply RingHom.ext
    intro r
    change (Spec.map (CommRingCat.ofHom f)).stalkMap q (StructureSheaf.toStalk R p r) =
      (IsLocalization.map Sq f (hmap.symm ▸ p.asIdeal.primeCompl.le_comap_map) : Rp →+* Sq)
        (algebraMap R Rp r)
    rw [IsLocalization.map_eq]
    exact AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom f) q r
  rw [he]
  exact IsLocalization.ker_map Sq f hmap

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ClosedStalkKernel
