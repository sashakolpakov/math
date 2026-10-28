import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.ModelAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.LogarithmicOverlap
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.LocalSmoothness

/-! # Logarithmic Affine Bounds -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Native global logarithmic differential ideals, with exact affine restrictions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type} {D : β → X.IdealSheafData}

def GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.openCover (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) : X.OpenCover :=
  Scheme.Cover.mkOfCovers A.indices (fun i => Spec (A.rings i)) A.map
    (by
      intro x
      have hx : x ∈ ⨆ i, (A.map i).opensRange := by rw [A.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.mp hx)
    (fun _ => inferInstance)

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.locallyNoetherian (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) : IsLocallyNoetherian X := by
  apply (isLocallyNoetherian_iff_openCover A.openCover).mpr
  intro i
  change A.indices at i
  let : Algebra.Smooth ℂ (A.rings i) := (A.model i).smooth
  let : IsNoetherianRing (A.rings i) := Algebra.FiniteType.isNoetherianRing ℂ (A.rings i)
  exact inferInstanceAs (IsLocallyNoetherian (Spec (A.rings i)))

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.existsUnique_logarithmicIdeal (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (J : X.IdealSheafData) (n : ℕ) :
    ∃! I : X.IdealSheafData, ∀ i, I.comap (A.map i) = Affine.QuotientKernel.Construction.affineQuotientKernel
      (Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal ℂ (A.equations i) (A.affineIdeal J i) n) := by
  apply Finite.OpenIdealSheafUniqueness.Construction.existsUnique_idealSheaf_of_finite_affine_cover (fun i => Spec (A.rings i)) A.map A.cover
  intro i j
  exact Global.LogarithmicOverlap.Construction.global_logarithmic_boundary_overlap f (A.rings i) (A.rings j)
    (A.map i) (A.map j) (A.ground i) (A.ground j) D (A.equations i) (A.equations j)
    (A.component i) (A.component j) (A.model i) (A.model j) J
    (A.affineIdeal J i) (A.affineIdeal J j) (A.affineIdeal_eq J i) (A.affineIdeal_eq J j) n

def GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (J : X.IdealSheafData) (n : ℕ) : X.IdealSheafData :=
  (A.existsUnique_logarithmicIdeal J n).choose

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_restrict (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (J : X.IdealSheafData) (n : ℕ)
    (i : A.indices) : (A.logarithmicIdeal J n).comap (A.map i) = Affine.QuotientKernel.Construction.affineQuotientKernel
      (Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal ℂ (A.equations i) (A.affineIdeal J i) n) :=
  (A.existsUnique_logarithmicIdeal J n).choose_spec.1 i

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_restrict_etale
    (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (J : X.IdealSheafData) (n : ℕ)
    (R : CommRingCat) [Algebra ℂ R] (j : Spec R ⟶ X) [Etale j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (w : β → R)
    (hw : ∀ l, (D l).comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w l}))
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel ℂ R β w) (K : Ideal R) (hK : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K) :
    (A.logarithmicIdeal J n).comap j = Affine.QuotientKernel.Construction.affineQuotientKernel
      (Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal ℂ w K n) := by
  let : Algebra.Smooth ℂ R := M.smooth
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℂ R
  have hcover : ⨆ i, (pullback.snd (A.map i) j).opensRange = ⊤ := by
    simp_rw [Scheme.Hom.opensRange_pullbackSnd]
    rw [← Scheme.Hom.preimage_iSup, A.cover, Scheme.Hom.preimage_top]
  let C : (Spec R).OpenCover := Scheme.Cover.mkOfCovers A.indices
    (fun i => pullback (A.map i) j) (fun i => pullback.snd (A.map i) j)
    (by
      intro x
      have hx : x ∈ ⨆ i, (pullback.snd (A.map i) j).opensRange := by rw [hcover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.mp hx)
    (fun _ => inferInstance)
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ C
  intro i
  change A.indices at i
  change ((A.logarithmicIdeal J n).comap j).comap (pullback.snd (A.map i) j) = _
  rw [← Scheme.IdealSheafData.comap_comp, ← pullback.condition, Scheme.IdealSheafData.comap_comp,
    A.logarithmicIdeal_restrict]
  exact Global.LogarithmicOverlap.Construction.global_logarithmic_boundary_overlap f (A.rings i) R (A.map i) j (A.ground i) hj
    D (A.equations i) w (A.component i) hw (A.model i) M J
    (A.affineIdeal J i) K (A.affineIdeal_eq J i) hK n

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_eq_atlas (A B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (J : X.IdealSheafData) (n : ℕ) :
    A.logarithmicIdeal J n = B.logarithmicIdeal J n := by
  let : IsLocallyNoetherian X := A.locallyNoetherian
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ B.openCover
  intro i
  change B.indices at i
  change (A.logarithmicIdeal J n).comap (B.map i) = (B.logarithmicIdeal J n).comap (B.map i)
  rw [B.logarithmicIdeal_restrict]
  exact A.logarithmicIdeal_restrict_etale J n (B.rings i) (B.map i) (B.ground i)
    (B.equations i) (B.component i) (B.model i) (B.affineIdeal J i) (B.affineIdeal_eq J i)

end

/-! Affine logarithmic bounds in arbitrary local boundary charts imply native global logarithmic bounds. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_unit_on_affine
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type} {D : β → X.IdealSheafData}
    (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (J : X.IdealSheafData) (n : ℕ)
    (R : CommRingCat) [Algebra ℂ R] (j : Spec R ⟶ X) [Etale j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (w : β → R)
    (hw : ∀ l, (D l).comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w l}))
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ R w) (K : Ideal R) (hK : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K)
    (hbound : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal ℂ w K n = ⊤) :
    (A.logarithmicIdeal J n).comap j = ⊤ := by
  classical
  let : Algebra.Smooth ℂ R := hboundary.smooth
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℂ R
  let C (p : PrimeSpectrum R) := Classical.choice (hboundary p)
  let q (p : PrimeSpectrum R) := Spec.map (CommRingCat.ofHom (C p).map.toRingHom)
  let E : (Spec R).OpenCover := Scheme.Cover.mkOfCovers (PrimeSpectrum R)
    (fun p => Spec (C p).carrier) q
    (fun p => ⟨p, (C p).point, (C p).point_over⟩) (fun _ => inferInstance)
  apply DifferentialUnitGluing.Construction.idealSheaf_eq_top_of_openCover _ E
  intro p
  change PrimeSpectrum R at p
  change ((A.logarithmicIdeal J n).comap j).comap (q p) = ⊤
  have hq : q p ≫ j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (C p).carrier := by
    rw [hj, ← Spec.map_comp]
    apply congrArg Spec.map
    ext c
    exact (C p).map.commutes c
  have hD (l : β) : (D l).comap (q p ≫ j) =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {(C p).map (w l)}) := by
    rw [Scheme.IdealSheafData.comap_comp, hw l]
    change (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w l})).comap
      (Spec.map (CommRingCat.ofHom (C p).map.toRingHom)) = _
    rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Ideal.map_span, Set.image_singleton]
  have hJ : J.comap (q p ≫ j) = Affine.QuotientKernel.Construction.affineQuotientKernel (K.map (C p).map.toRingHom) := by
    rw [Scheme.IdealSheafData.comap_comp, hK]
    exact Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom K (C p).map.toRingHom
  have hb : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal ℂ (fun l => (C p).map (w l))
      (K.map (C p).map.toRingHom) n = ⊤ := by
    let : Algebra R (C p).carrier := (C p).map.toRingHom.toAlgebra
    let : IsScalarTower ℂ R (C p).carrier :=
      IsScalarTower.of_algebraMap_eq (fun c => ((C p).map.commutes c).symm)
    let : Algebra.Etale R (C p).carrier := (HasRingHomProperty.Spec_iff (P := @Etale)).mp
      (inferInstance : Etale (Spec.map (CommRingCat.ofHom (C p).map.toRingHom)))
    exact Relative.LogarithmicBoundary.Construction.relative_logarithmic_order_bound_map (S := (C p).carrier) ℂ w K n hbound
  rw [← Scheme.IdealSheafData.comap_comp,
    A.logarithmicIdeal_restrict_etale J n (C p).carrier (q p ≫ j)
      (by rw [Category.assoc]; exact hq) (fun l => (C p).map (w l)) hD
      (C p).model (K.map (C p).map.toRingHom) hJ, hb, DifferentialUnitGluing.Construction.affineQuotientKernel_top]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
