import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CenterSmooth
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.AffineCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.ComplexNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.ComplexAffineDifferentialIdeal

/-! # Pointed Smooth Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.PointedSmoothCenter.Construction

noncomputable section

/-! Pointed actual affine open charts detect smoothness of native closed subschemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem kernel_subscheme_smooth_of_closed_immersion
    {Z X B : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ B) [IsClosedImmersion i] [Smooth (i ≫ f)] :
    Smooth (i.ker.subschemeι ≫ f) := by
  have hi : inv i.toImage ≫ i = i.imageι := (IsIso.inv_comp_eq i.toImage).mpr i.toImage_imageι.symm
  have he : inv i.toImage ≫ (i ≫ f) = i.ker.subschemeι ≫ f := by
    rw [← Category.assoc, hi]
  exact he ▸ (inferInstance : Smooth (inv i.toImage ≫ (i ≫ f)))

theorem idealSheaf_subscheme_smooth_of_open_charts
    {X B : Scheme.{u}} {ι : Type v} (I : X.IdealSheafData) (f : X ⟶ B)
    (U : ι → Scheme.{u}) (j : ∀ a, U a ⟶ X) [∀ a, IsOpenImmersion (j a)]
    (hcover : ⨆ a, (j a).opensRange = ⊤)
    (hlocal : ∀ a, Smooth ((I.comap (j a)).subschemeι ≫ j a ≫ f)) :
    Smooth (I.subschemeι ≫ f) := by
  let k : ∀ a, (I.comap (j a)).subscheme ⟶ I.subscheme := fun a =>
    (I.comapIso (j a)).hom ≫ pullback.snd (j a) I.subschemeι
  have hcomp (a : ι) : k a ≫ I.subschemeι = (I.comap (j a)).subschemeι ≫ j a := by
    dsimp only [k]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have hrange (a : ι) : (k a).opensRange = I.subschemeι ⁻¹ᵁ (j a).opensRange := by
    dsimp only [k]
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackSnd]
  have hsource : ⨆ a, (k a).opensRange = ⊤ := by
    simp_rw [hrange]
    rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]
  let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) (fun a => (k a).opensRange) hsource
  intro a
  let : Smooth (k a ≫ (I.subschemeι ≫ f)) := by
    rw [← Category.assoc, hcomp, Category.assoc]
    exact hlocal a
  exact SupportedBlowupSmoothGluing.Construction.smooth_on_opensRange_of_open_immersion (I.subschemeι ≫ f) (k a)

theorem affineQuotientKernel_complex_subscheme_smooth
    (R : CommRingCat) [Algebra ℂ R] (K : Ideal R) [Algebra.Smooth ℂ (R ⧸ K)] :
    Smooth ((Affine.QuotientKernel.Construction.affineQuotientKernel K).subschemeι ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) := by
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))
  let : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have he : i ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (R ⧸ K) := by
    rw [ComplexAffineDifferentialIdeal.Construction.complexSpecStructure, ← Spec.map_comp]
    rfl
  let : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (R ⧸ K)) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (algebraMap ℂ (R ⧸ K)))).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  let : Smooth (i ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) := he.symm ▸ inferInstance
  exact kernel_subscheme_smooth_of_closed_immersion i (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R)

theorem idealSheaf_complex_center_smooth_of_pointed_open_charts
    {X : Scheme} (I : X.IdealSheafData) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (hlocal : ∀ x : X, ∃ (R : CommRingCat) (_ : Algebra ℂ R) (j : Spec R ⟶ X),
      IsOpenImmersion j ∧ j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R ∧
      ∃ q : PrimeSpectrum R, j q = x ∧ ∃ K : Ideal R,
        I.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K ∧ Algebra.Smooth ℂ (R ⧸ K)) :
    Smooth (I.subschemeι ≫ f) := by
  classical
  choose R aR j hj hg q hq K hK hs using hlocal
  let : ∀ x, Algebra ℂ (R x) := aR
  let : ∀ x, IsOpenImmersion (j x) := hj
  have hcover : ⨆ x, (j x).opensRange = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, q x, hq x⟩
  apply idealSheaf_subscheme_smooth_of_open_charts I f (fun x => Spec (R x)) j hcover
  intro x
  rw [hK, hg]
  let : Algebra.Smooth ℂ (R x ⧸ K x) := hs x
  exact affineQuotientKernel_complex_subscheme_smooth (R x) (K x)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.PointedSmoothCenter.Construction
