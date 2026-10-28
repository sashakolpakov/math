import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.CenterRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceBoundIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceBoundOverlap

/-! # Bound Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A finite coefficient bound on one global atlas holds on every actual étale affine chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.hasBound_restrict_etale (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (m : ℕ)
    (hb : ∀ i, (A.choice i).HasBound m) (R : CommRingCat)
    [Algebra ℂ R] [Algebra ℚ R] [Algebra.Smooth ℂ R]
    (j : Spec R ⟶ X) [Etale j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (L : Ideal R) (hL : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel L)
    (C : Component.CenterChoice.Construction.ComponentCenterChoice ℂ R L n) : C.HasBound m := by
  have hcover : (⨆ i, (pullback.snd (A.map i) j).opensRange) = ⊤ := by
    simp_rw [Scheme.Hom.opensRange_pullbackSnd]
    rw [← Scheme.Hom.preimage_iSup, A.cover, Scheme.Hom.preimage_top]
  let 𝒰 : (Spec R).OpenCover := Scheme.Cover.mkOfCovers A.indices
    (fun i => pullback (A.map i) j) (fun i => pullback.snd (A.map i) j)
    (by
      intro x
      have hx : x ∈ ⨆ i, (pullback.snd (A.map i) j).opensRange := by rw [hcover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.mp hx)
    (fun _ => inferInstance)
  apply (C.boundIdeal_eq_top_iff m).mp
  apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
  rw [DifferentialUnitGluing.Construction.affineQuotientKernel_top]
  apply DifferentialUnitGluing.Construction.idealSheaf_eq_top_of_openCover _ 𝒰
  intro i
  change A.indices at i
  change (Affine.QuotientKernel.Construction.affineQuotientKernel (C.boundIdeal m)).comap (pullback.snd (A.map i) j) = ⊤
  apply GlobalCoefficient.ComponentGluing.Construction.idealSheaf_eq_of_fromSpec
  intro W
  let P := pullback (A.map i) j
  let S := Γ(P, W)
  let u : Spec (.of S) ⟶ Spec (A.rings i) := W.2.fromSpec ≫ pullback.fst (A.map i) j
  let v : Spec (.of S) ⟶ Spec R := W.2.fromSpec ≫ pullback.snd (A.map i) j
  let φ : A.rings i →+* S := (Spec.preimage u).hom
  let ψ : R →+* S := (Spec.preimage v).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = u := Spec.map_preimage u
  have hψ : Spec.map (CommRingCat.ofHom ψ) = v := Spec.map_preimage v
  have hcomm : u ≫ A.map i = v ≫ j := by
    dsimp only [u, v]
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hbase : φ.comp (algebraMap ℂ (A.rings i)) = ψ.comp (algebraMap ℂ R) := by
    have he : CommRingCat.ofHom (φ.comp (algebraMap ℂ (A.rings i))) =
        CommRingCat.ofHom (ψ.comp (algebraMap ℂ R)) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom (algebraMap ℂ (A.rings i)) ≫ CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ R) ≫ CommRingCat.ofHom ψ)
      rw [Spec.map_comp, Spec.map_comp, hφ, hψ]
      change u ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (A.rings i) = v ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R
      rw [← A.ground i, ← hj]
      simpa only [Category.assoc] using congrArg (fun m => m ≫ f) hcomm
    exact congrArg CommRingCat.Hom.hom he
  let : Algebra ℂ S := (φ.comp (algebraMap ℂ (A.rings i))).toAlgebra
  let φₖ : A.rings i →ₐ[ℂ] S := { __ := φ, commutes' := fun _ => rfl }
  let ψₖ : R →ₐ[ℂ] S := { __ := ψ, commutes' := fun c => (RingHom.congr_fun hbase c).symm }
  let : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  have hφe : φₖ.toRingHom.Etale := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    exact inferInstanceAs (Etale u)
  have hψe : ψₖ.toRingHom.Etale := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    exact inferInstanceAs (Etale v)
  have hJL : (A.ideals i).map φ = L.map ψ := by
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    rw [← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, ← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, hφ, hψ,
      ← A.ideal_eq i, ← hL, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomm]
  have hc := Component.CenterChoice.Construction.ComponentCenterChoice.hasBound_on_common_refinement φₖ ψₖ hφe hψe hJL
    (A.choice i) C (hb i)
  have he : (C.boundIdeal m).map ψ = ⊤ := by
    rw [C.boundIdeal_map_etale ψₖ hψe m]
    exact ((C.mapEtale ψₖ hψe).boundIdeal_eq_top_iff m).mpr hc
  rw [Scheme.IdealSheafData.comap_top, ← Scheme.IdealSheafData.comap_comp]
  change (Affine.QuotientKernel.Construction.affineQuotientKernel (C.boundIdeal m)).comap v = ⊤
  rw [← hψ, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, he, DifferentialUnitGluing.Construction.affineQuotientKernel_top]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
