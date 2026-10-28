import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImageStalkKernel
import OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedSurjectionKernel

/-! # Support Kernel -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SupportKernel.Constructions

noncomputable section

/-! The original reduced support of an affine closed immersion has
exactly the localized defining ideal in the canonical affine stalk
coordinates. All comparisons use the actual maps and their squares. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImageStalkKernel.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedSurjectionKernel.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem map_kernel_iso {R S R' S' : CommRingCat} (a : R ≅ R') (b : S ≅ S')
    (f : R ⟶ S) (g : R' ⟶ S') (h : a.hom ≫ g = f ≫ b.hom) :
    (RingHom.ker f.hom).map a.hom.hom = RingHom.ker g.hom := by
  have hc : (RingHom.ker g.hom).comap a.hom.hom = RingHom.ker f.hom := by
    ext r
    change g (a.hom r) = 0 ↔ f r = 0
    have he : g (a.hom r) = b.hom (f r) := ConcreteCategory.congr_hom h r
    constructor
    · intro hz
      apply (ConcreteCategory.bijective_of_isIso b.hom).1
      exact (he.symm.trans hz).trans (map_zero b.hom.hom).symm
    · intro hz
      exact he.trans ((congrArg b.hom hz).trans (map_zero b.hom.hom))
  rw [← hc]
  exact Ideal.map_comap_of_surjective _ (ConcreteCategory.bijective_of_isIso a.hom).2 _

theorem spec_stalk_kernel {R S : CommRingCat} (f : R ⟶ S) (hf : Function.Surjective f) (q : PrimeSpectrum S) :
    (RingHom.ker ((Spec.map f).stalkMap q).hom).map (Spec.stalkIso R (q.comap f.hom)).hom.hom =
      (RingHom.ker f.hom).map (algebraMap R (Localization.AtPrime (q.comap f.hom).asIdeal)) := by
  have h := map_kernel_iso (Spec.stalkIso R (q.comap f.hom)) (Spec.stalkIso S q)
    ((Spec.map f).stalkMap q)
    (CommRingCat.ofHom (Localization.localRingHom (q.comap f.hom).asIdeal q.asIdeal f.hom rfl))
    (Scheme.arrowStalkMapSpecIso f q).hom.w
  exact h.trans (LocalizedSurjectionKernel.Constructions.localRingHom_kernel f.hom hf q)

variable (R S : CommRingCat) [IsDomain S] (f : R ⟶ S) (hf : Function.Surjective f)

include hf in
theorem support_kernel_localization (q : PrimeSpectrum S) :
    ((StalkPrimeQuotient.Constructions.kernelPrime (Spec R) (Geometric.StratumClosure.integralImageClosure (Spec.map f)) ((Spec.map f) q) (Closed.ImageStalkKernel.Constructions.image_mem (Spec.map f) q)).asIdeal).map
      (Spec.stalkIso R (q.comap f.hom)).hom.hom =
      (RingHom.ker f.hom).map (algebraMap R (Localization.AtPrime (q.comap f.hom).asIdeal)) := by
  let : IsClosedImmersion (Spec.map f) := IsClosedImmersion.spec_of_surjective f hf
  rw [Closed.ImageStalkKernel.Constructions.kernelPrime_eq_stalkMap_kernel]
  exact spec_stalk_kernel f hf q

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SupportKernel.Constructions
