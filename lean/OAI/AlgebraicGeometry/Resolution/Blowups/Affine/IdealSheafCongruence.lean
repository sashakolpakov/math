import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruentMaps
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.AffinePullback

/-! # Ideal Sheaf Congruence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealSheafCongruence.Construction

noncomputable section

/-! The proved algebraic congruence of comparison maps is intrinsic congruence of their actual affine scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem scheme_maps_agree_on_kernel_of_closed
    {Z U X : Scheme.{u}} (j : Z ⟶ U) [IsClosedImmersion j] (a b : U ⟶ X) (h : j ≫ a = j ≫ b) :
    j.ker.subschemeι ≫ a = j.ker.subschemeι ≫ b := by
  apply (cancel_epi j.toImage).mp
  change j.toImage ≫ (j.imageι ≫ a) = j.toImage ≫ (j.imageι ≫ b)
  simpa only [← Category.assoc, j.toImage_imageι] using h

theorem idealSheafCongruent_Spec_of_congruence
    {R S : Type u} [CommRing R] [CommRing S] (f g : R →+* S) (T : Ideal R)
    (hT : T.map f = T.map g) (hdiff : ∀ x : R, g x - f x ∈ T.map f) :
    IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom g))
      (QuotientKernel.Construction.affineQuotientKernel T) := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (T.map f)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  constructor
  · rw [IdealChartDescent.Construction.affineQuotientKernel_comap_hom, IdealChartDescent.Construction.affineQuotientKernel_comap_hom, hT]
  · rw [IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
    apply scheme_maps_agree_on_kernel_of_closed
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (T.map f))))
    have he : (Ideal.Quotient.mk (T.map f)).comp f = (Ideal.Quotient.mk (T.map f)).comp g := by
      apply RingHom.ext
      intro x
      exact (Ideal.Quotient.eq.mpr (hdiff x)).symm
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (congrArg CommRingCat.ofHom he)

theorem idealSheafCongruent_Spec_iff
    {R S : Type u} [CommRing R] [CommRing S] (f g : R →+* S) (T : Ideal R) :
    IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom g))
      (QuotientKernel.Construction.affineQuotientKernel T) ↔ T.map f = T.map g ∧ (∀ x : R, g x - f x ∈ T.map f) := by
  constructor
  · intro h
    have hT : QuotientKernel.Construction.affineQuotientKernel (T.map f) = QuotientKernel.Construction.affineQuotientKernel (T.map g) := by
      simpa only [IdealChartDescent.Construction.affineQuotientKernel_comap_hom] using h.1
    refine ⟨(GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp hT, ?_⟩
    let q := Ideal.Quotient.mk (T.map f)
    let j := Spec.map (CommRingCat.ofHom q)
    have hr : (QuotientKernel.Construction.affineQuotientKernel (T.map f)).subschemeι ≫ Spec.map (CommRingCat.ofHom f) =
        (QuotientKernel.Construction.affineQuotientKernel (T.map f)).subschemeι ≫ Spec.map (CommRingCat.ofHom g) := by
      rw [← IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
      exact h.2
    have hm := congrArg (fun m => j.toImage ≫ m) hr
    have hspec : j ≫ Spec.map (CommRingCat.ofHom f) = j ≫ Spec.map (CommRingCat.ofHom g) := by
      change j.toImage ≫ (j.imageι ≫ Spec.map (CommRingCat.ofHom f)) =
        j.toImage ≫ (j.imageι ≫ Spec.map (CommRingCat.ofHom g)) at hm
      simpa only [← Category.assoc, j.toImage_imageι] using hm
    have he : CommRingCat.ofHom (q.comp f) = CommRingCat.ofHom (q.comp g) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom f ≫ CommRingCat.ofHom q) =
        Spec.map (CommRingCat.ofHom g ≫ CommRingCat.ofHom q)
      rw [Spec.map_comp, Spec.map_comp]
      exact hspec
    intro x
    exact Ideal.Quotient.eq.mp (RingHom.congr_fun (congrArg CommRingCat.Hom.hom he) x).symm
  · rintro ⟨hT, hdiff⟩
    exact idealSheafCongruent_Spec_of_congruence f g T hT hdiff

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealSheafCongruence.Construction
