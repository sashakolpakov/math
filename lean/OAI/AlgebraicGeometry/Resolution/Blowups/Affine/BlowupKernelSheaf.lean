import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedCarrierCenters
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ClosedMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.ControlledIdealNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceBlowupKernel

/-! # Blowup Kernel Sheaf -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupKernelSheaf.Construction

noncomputable section

/-! Exact native kernel sheaves for affine blowup comparisons and framed hypersurfaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem specMap_kernel_eq_affineQuotientKernel {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) :
    (Spec.map (CommRingCat.ofHom φ)).ker = QuotientKernel.Construction.affineQuotientKernel (RingHom.ker φ) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [QuotientKernel.Construction.affineQuotientKernel_idealTop, Scheme.Hom.ker_apply]
  change RingHom.ker (Spec.map (CommRingCat.ofHom φ)).appTop.hom = _
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso (.of S)).commRingCatIsoToRingEquiv]
  change RingHom.ker ((Spec.map (CommRingCat.ofHom φ)).appTop ≫
    (Scheme.ΓSpecIso (.of S)).hom).hom = _
  rw [Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, ← RingHom.comap_ker]
  rfl

theorem affineBlowupMap_ker_comap_chart {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (φ : R →+* S) (hφ : Function.Surjective φ) (a : I) :
    (ReesMap.Construction.affineBlowupMap I φ).ker.comap
      (Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I a) (Blowup.Charts.Construction.reesGenerator_mem I a) (by decide)) =
      QuotientKernel.Construction.affineQuotientKernel (RingHom.ker (ChartLift.Construction.blowupChartMap I φ a)) := by
  let : IsClosedImmersion (ReesMap.Construction.affineBlowupMap I φ) := Blowup.ClosedMap.Construction.affineBlowupMap_isClosedImmersion I φ hφ
  rw [ClosedCarrierCenters.Construction.kernel_comap_of_closed_pullback _ _ _ _ (Blowup.FlatBaseChange.Construction.affineBlowupMap_chart_isPullback I φ a),
    specMap_kernel_eq_affineQuotientKernel]

/-- A smooth normal frame identifies the closed hypersurface blowup with the
native controlled hypersurface ideal on the entire affine ambient blowup. -/
theorem framed_hypersurface_affineBlowup_ker
    {k R ι : Type u} [CommRing k] [CommRing R] [Algebra k R]
    [IsNoetherianRing R] [Algebra ℚ R] [DecidableEq ι]
    (I : Ideal R) (g : ι → I) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j).val = if i = j then 1 else 0)
    (hgen : Ideal.span (Set.range (fun i => (g i).val)) = I) (j : ι) :
    (ReesMap.Construction.affineBlowupMap I (Ideal.Quotient.mk (Ideal.span {(g j).val}))).ker =
      ControlledIdealNaturality.Construction.affineControlledIdealSheaf I (Ideal.span {(g j).val}) 1 := by
  let : IsLocallyNoetherian (ReesGrading.Construction.affineBlowup I) :=
    LocallyOfFiniteType.isLocallyNoetherian (ReesGrading.Construction.affineBlowupToSpec I)
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (GeneratedBlowupCover.Construction.affineBlowupGeneratorAffineCover I g hgen).openCover
  intro i
  change ι at i
  change (ReesMap.Construction.affineBlowupMap I (Ideal.Quotient.mk (Ideal.span {(g j).val}))).ker.comap
      (Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I (g i)) (Blowup.Charts.Construction.reesGenerator_mem I (g i)) (by decide)) =
    (ControlledIdealNaturality.Construction.affineControlledIdealSheaf I (Ideal.span {(g j).val}) 1).comap
      (Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I (g i)) (Blowup.Charts.Construction.reesGenerator_mem I (g i)) (by decide))
  rw [affineBlowupMap_ker_comap_chart I _ Ideal.Quotient.mk_surjective,
    ControlledIdealNaturality.Construction.affineControlledIdealSheaf_comap_chart]
  exact congrArg QuotientKernel.Construction.affineQuotientKernel (HypersurfaceBlowupKernel.Construction.framed_hypersurface_blowupChart_ker I g D hD i j)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupKernelSheaf.Construction
