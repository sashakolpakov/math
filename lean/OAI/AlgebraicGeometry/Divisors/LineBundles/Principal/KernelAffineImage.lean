import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealAffineCover

/-! # Kernel Affine Image -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.KernelAffineImage.BundleCycles

noncomputable section

/-! A principal kernel on an actual affine pullback chart descends to the restriction of the original global section on the chart's affine image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Z A B : Scheme.{0}} (f : Z ⟶ X) [QuasiCompact f]
  (j : A ⟶ X) [IsOpenImmersion j] [IsAffine A]
  (a : B ⟶ Z) (b : B ⟶ A) (hp : IsPullback b a j f)
  (s : Γ(X, ⊤)) (hk : RingHom.ker b.appTop.hom = Ideal.span {j.appTop s})

omit [IsAffine A] in
theorem openImage_section_restriction :
    X.presheaf.map (homOfLE (show j ''ᵁ (⊤ : A.Opens) ≤ ⊤ from le_top)).op ≫
      (j.appIso ⊤).hom = j.appTop := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  exact j.appLE_eq_app

include hp hk in
theorem principalKernel_on_affineImage :
    RingHom.ker (f.app (j ''ᵁ (⊤ : A.Opens))).hom =
      Ideal.span {X.presheaf.map (homOfLE (show j ''ᵁ (⊤ : A.Opens) ≤ ⊤ from le_top)).op s} := by
  let : QuasiCompact b := MorphismProperty.of_isPullback hp.flip inferInstance
  let U : X.affineOpens := ⟨j ''ᵁ (⊤ : A.Opens), (isAffineOpen_top A).image_of_isOpenImmersion j⟩
  let e : Γ(X, U.1) ≅ Γ(A, ⊤) := j.appIso ⊤
  have hbase := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f b a j hp
    (⟨⊤, isAffineOpen_top A⟩ : A.affineOpens)
  have hc : RingHom.ker b.appTop.hom = (RingHom.ker (f.app U.1).hom).comap e.inv.hom :=
    (Scheme.Hom.ker_apply b ⟨⊤, isAffineOpen_top A⟩).symm.trans
      (hbase.trans (congrArg (Ideal.comap e.inv.hom) (Scheme.Hom.ker_apply f U)))
  have hmap := congrArg (Ideal.map e.inv.hom) (hc.symm.trans hk)
  have hker : RingHom.ker (f.app U.1).hom = Ideal.span {e.inv (j.appTop s)} :=
    (Ideal.map_comap_of_surjective e.inv.hom (ConcreteCategory.bijective_of_isIso e.inv).2
      (RingHom.ker (f.app U.1).hom)).symm.trans
      (hmap.trans (by rw [Ideal.map_span, Set.image_singleton]))
  have he : e.inv (j.appTop s) = X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op s := by
    have h := ConcreteCategory.congr_hom (openImage_section_restriction j) s
    have hv := congrArg e.inv h
    exact hv.symm.trans (ConcreteCategory.congr_hom e.hom_inv_id _)
  exact hker.trans (congrArg (fun t => Ideal.span {t}) he)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.KernelAffineImage.BundleCycles
