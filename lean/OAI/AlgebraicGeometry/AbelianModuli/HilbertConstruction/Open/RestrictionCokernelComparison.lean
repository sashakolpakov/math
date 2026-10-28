import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AdditiveSheafRestrictionLimits

/-! # Restriction Cokernel Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionCokernelComparison.ZariskiCohomology.LocalKilling

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

theorem openRestrictionPushforward_map_mono {X : Scheme.{u}}
    (U : X.Opens)
    {F G : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X} (f : F ⟶ G) [Mono f] :
    Mono ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).map f) := by
  have : Mono f.hom := by
    change Mono ((sheafToPresheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).map f)
    infer_instance
  have hmono : Mono ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).map f).hom := by
    exact (NatTrans.mono_iff_mono_app _).mpr fun V ↦ by
      change Mono (f.hom.app _)
      infer_instance
  exact Functor.mono_of_mono_map
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hmono

theorem openRestrictionPushforward_map_epi_of_affine_app_surjective
    {R : CommRingCat.{u}} (U : (Spec R).Opens) (hU : IsAffineOpen U)
    {F G : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf (Spec R)} (f : F ⟶ G)
    (hf : ∀ (W : (Spec R).Opens), IsAffineOpen W →
      Function.Surjective (f.hom.app (op W))) :
    Epi ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).map f) := by
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi
    ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).map f)).1
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro W t x hxW
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
  let A := U.ι.isOpenEmbedding.functor.obj
    ((Opens.map U.ι.base).obj V)
  have hA : A = U ⊓ V := by
    ext y
    change (∃ z : U, z.1 ∈ V ∧ z.1 = y) ↔ y ∈ U ∧ y ∈ V
    constructor
    · rintro ⟨z, hzV, rfl⟩
      exact ⟨z.2, hzV⟩
    · rintro ⟨hyU, hyV⟩
      exact ⟨⟨y, hyU⟩, hyV, rfl⟩
  have hAaffine : IsAffineOpen A := by
    rw [hA]
    exact hU.inf hV
  let tV := ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj G).1.map
    (homOfLE hVW).op t
  obtain ⟨s, hs⟩ := hf A hAaffine tV
  refine ⟨V, hVW, ⟨s, ?_⟩, hxV⟩
  exact hs

theorem openRestrictionPushforward_cokernelComparison_mono
    {X : Scheme.{u}} (U : X.Opens)
    {F G : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X} (f : F ⟶ G) [Mono f] :
    Mono (cokernelComparison f (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U)) := by
  let E := AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.Exact := ShortComplex.cokernelSequence_exact f
  have hT : (S.map E).Exact :=
    hS.map_of_mono_of_preservesKernel E (by infer_instance) (by infer_instance)
  dsimp [S] at hT
  change (ShortComplex.mk (E.map f) (E.map (cokernel.π f)) _).Exact at hT
  let e : cokernel (E.map f) ≅ image (E.map (cokernel.π f)) :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (E.map f))
      hT.isColimitImage
  have he_fac : cokernel.π (E.map f) ≫ e.hom =
      factorThruImage (E.map (cokernel.π f)) := by
    simpa [e] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (cokernelIsCokernel (E.map f)) hT.isColimitImage
          WalkingParallelPair.one)
  have he : cokernelComparison f E =
      e.hom ≫ image.ι (E.map (cokernel.π f)) := by
    rw [← cancel_epi (cokernel.π (E.map f))]
    rw [π_comp_cokernelComparison]
    symm
    rw [← Category.assoc, he_fac, image.fac]
  rw [he]
  infer_instance

theorem openRestrictionPushforward_cokernelComparison_isIso_of_affine_app_surjective
    {R : CommRingCat.{u}} (U : (Spec R).Opens) (hU : IsAffineOpen U)
    {F G : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf (Spec R)} (f : F ⟶ G) [Mono f]
    (hf : ∀ (W : (Spec R).Opens), IsAffineOpen W →
      Function.Surjective ((cokernel.π f).hom.app (op W))) :
    IsIso (cokernelComparison f (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U)) := by
  let E := AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U
  let μ := cokernelComparison f E
  let : Mono μ := by
    dsimp [μ, E]
    exact openRestrictionPushforward_cokernelComparison_mono U f
  let : Epi (E.map (cokernel.π f)) := by
    dsimp [E]
    exact openRestrictionPushforward_map_epi_of_affine_app_surjective
      U hU (cokernel.π f) hf
  let : Epi μ := by
    exact epi_of_epi_fac (π_comp_cokernelComparison f E)
  exact isIso_of_mono_of_epi μ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionCokernelComparison.ZariskiCohomology.LocalKilling
