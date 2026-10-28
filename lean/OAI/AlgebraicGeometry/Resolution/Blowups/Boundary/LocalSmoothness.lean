import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IntersectionCenters
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Smooth
import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedBlowupSmoothGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.GeneratedBlowupCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.QuotientBaseChange

/-! # Local Smoothness -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Smoothness of an ambient ring and its actual boundary-intersection blowups from local models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.smooth
    {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} {w : ι → R} (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) : Algebra.Smooth k R := by
  let B (p : PrimeSpectrum R) := (h p).some
  let f := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let j (p : PrimeSpectrum R) := Spec.map (CommRingCat.ofHom (B p).map.toRingHom)
  let : ∀ p, IsOpenImmersion (j p) := fun p => (B p).isOpenImmersion
  have hcover : ⨆ p, (j p).opensRange = ⊤ := by
    apply top_le_iff.mp
    intro p _
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨p, (B p).point, (B p).point_over⟩
  have hlocal (p : PrimeSpectrum R) : Smooth (j p ≫ f) := by
    have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (B p).carrier))) :=
      (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
        (RingHom.smooth_algebraMap.mpr (B p).model.smooth)
    have he : j p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (B p).carrier)) := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact (B p).map.commutes x
    rwa [he]
  have hs : Smooth f := by
    let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
    apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) (fun p => (j p).opensRange) hcover
    intro p
    let : Smooth (j p ≫ f) := hlocal p
    exact SupportedBlowupSmoothGluing.Construction.smooth_on_opensRange_of_open_immersion f (j p)
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.intersection_blowup_smooth
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type u} {w : ι → R} (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (C : Finset ι) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec (Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  let I := Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C
  let g : C → I := Boundary.Schedule.Construction.boundaryIntersectionGenerator w C
  have hgen : Ideal.span (Set.range (fun i => (g i).val)) = I := rfl
  let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth)
    (GeneratedBlowupCover.Construction.affineBlowupGeneratorAffineCover I g hgen).openCover
  intro i
  change C at i
  have hs : Algebra.Smooth k (Blowup.Charts.Construction.blowupChart I (g i)) := (h.blowup_intersection C i).smooth
  change Smooth (Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I (g i))
    (Blowup.Charts.Construction.reesGenerator_mem I (g i)) (by decide) ≫
      (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))))
  rw [← Category.assoc, Blowup.Charts.Construction.affineBlowup_chart_structureMap, ← Spec.map_comp]
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr hs)

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.intersection_smooth
    {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} {w : ι → R} (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (C : Finset ι) :
    Algebra.Smooth k (R ⧸ Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C) := by
  let I := Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C
  let B (p : PrimeSpectrum R) := (h p).some
  let A (p : PrimeSpectrum R) : Type u := (B p).carrier
  let : ∀ p, Algebra R (A p) := fun p => (B p).map.toRingHom.toAlgebra
  let : ∀ p, IsScalarTower k R (A p) := fun p =>
    IsScalarTower.of_algebraMap_eq (fun x => ((B p).map.commutes x).symm)
  let Q := R ⧸ I
  let T (p : PrimeSpectrum R) := A p ⧸ I.map (algebraMap R (A p))
  let : ∀ p, IsScalarTower k Q (T p) := fun _ => Blowups.Smooth.TransformedCoordinateHypersurface.Construction.extendedQuotient_scalarTower I
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let f := Spec.map (CommRingCat.ofHom (algebraMap k Q))
  let r (p : PrimeSpectrum R) := Spec.map (CommRingCat.ofHom (algebraMap R (A p)))
  let j (p : PrimeSpectrum R) := Spec.map (CommRingCat.ofHom (algebraMap Q (T p)))
  let g (p : PrimeSpectrum R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R (A p)))))
  let : ∀ p, IsOpenImmersion (r p) := fun p => (B p).isOpenImmersion
  have hpb (p : PrimeSpectrum R) : IsPullback (j p) (g p) q (r p) :=
    Affine.QuotientBaseChange.Construction.affineQuotient_baseChange_isPullback (S := A p) I
  let : ∀ p, IsOpenImmersion (j p) := fun p =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hpb p).flip inferInstance
  have hrange (p : PrimeSpectrum R) : (j p).opensRange = q ⁻¹ᵁ (r p).opensRange :=
    SupportedBlowupSmoothGluing.Construction.opensRange_of_open_pullback (j p) (g p) q (r p) (hpb p)
  have hambient : ⨆ p, (r p).opensRange = ⊤ := by
    apply top_le_iff.mp
    intro p _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, (B p).point, (B p).point_over⟩
  have hcover : ⨆ p, (j p).opensRange = ⊤ := by
    simp_rw [hrange]
    rw [← Scheme.Hom.preimage_iSup, hambient, Scheme.Hom.preimage_top]
  have hlocal (p : PrimeSpectrum R) : Smooth (j p ≫ f) := by
    have hs : Algebra.Smooth k (T p) := by
      change Algebra.Smooth k (A p ⧸ I.map (B p).map.toRingHom)
      rw [Boundary.IntersectionCenters.Construction.boundaryIntersectionIdeal_map]
      exact (B p).model.intersection_smooth C
    rw [← Spec.map_comp]
    have he : CommRingCat.ofHom (algebraMap k Q) ≫ CommRingCat.ofHom (algebraMap Q (T p)) =
        CommRingCat.ofHom (algebraMap k (T p)) := by
      ext x
      exact (IsScalarTower.algebraMap_apply k Q (T p) x).symm
    rw [he]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr hs)
  have hs : Smooth f := by
    let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
    apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) (fun p => (j p).opensRange) hcover
    intro p
    let : Smooth (j p ≫ f) := hlocal p
    exact SupportedBlowupSmoothGluing.Construction.smooth_on_opensRange_of_open_immersion f (j p)
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
