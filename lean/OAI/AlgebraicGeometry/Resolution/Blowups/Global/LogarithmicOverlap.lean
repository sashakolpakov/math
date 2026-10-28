import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.LogarithmicNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ComponentGluing

/-! # Logarithmic Overlap -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.LogarithmicOverlap.Construction

noncomputable section

/-! Native logarithmic ideals agree on actual overlaps of étale boundary coordinate charts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem global_logarithmic_boundary_overlap
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (R S : CommRingCat.{u}) [Algebra k R] [Algebra k S]
    (j : Spec R ⟶ X) (l : Spec S ⟶ X) [Etale j] [Etale l]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (hl : l ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k S)))
    {β : Type v} (D : β → X.IdealSheafData) (w : β → R) (v : β → S)
    (hw : ∀ a, (D a).comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w a}))
    (hv : ∀ a, (D a).comap l = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {v a}))
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R β w) (N : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k S β v)
    (J : X.IdealSheafData) (A : Ideal R) (B : Ideal S)
    (hA : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel A) (hB : J.comap l = Affine.QuotientKernel.Construction.affineQuotientKernel B) (n : ℕ) :
    (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w A n)).comap (pullback.fst j l) =
      (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k v B n)).comap (pullback.snd j l) := by
  apply GlobalCoefficient.ComponentGluing.Construction.idealSheaf_eq_of_fromSpec
  intro W
  let P := pullback j l
  let T := Γ(P, W)
  let u : Spec (.of T) ⟶ Spec R := W.2.fromSpec ≫ pullback.fst j l
  let z : Spec (.of T) ⟶ Spec S := W.2.fromSpec ≫ pullback.snd j l
  let φ : R →+* T := (Spec.preimage u).hom
  let ψ : S →+* T := (Spec.preimage z).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = u := Spec.map_preimage u
  have hψ : Spec.map (CommRingCat.ofHom ψ) = z := Spec.map_preimage z
  have hcomm : u ≫ j = z ≫ l := by
    dsimp only [u, z]
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hbase : φ.comp (algebraMap k R) = ψ.comp (algebraMap k S) := by
    have he : CommRingCat.ofHom (φ.comp (algebraMap k R)) =
        CommRingCat.ofHom (ψ.comp (algebraMap k S)) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom (algebraMap k R) ≫ CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap k S) ≫ CommRingCat.ofHom ψ)
      rw [Spec.map_comp, Spec.map_comp, hφ, hψ, ← hj, ← hl]
      simpa only [Category.assoc] using congrArg (fun q => q ≫ f) hcomm
    exact congrArg CommRingCat.Hom.hom he
  let : Algebra k T := (φ.comp (algebraMap k R)).toAlgebra
  let φₖ : R →ₐ[k] T := { __ := φ, commutes' := fun _ => rfl }
  let ψₖ : S →ₐ[k] T := { __ := ψ, commutes' := fun c => (RingHom.congr_fun hbase c).symm }
  let : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  have hφe : φₖ.toRingHom.Etale := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    exact inferInstanceAs (Etale u)
  have hψe : ψₖ.toRingHom.Etale := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    exact inferInstanceAs (Etale z)
  have hAB : A.map φ = B.map ψ := by
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    rw [← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, ← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, hφ, hψ,
      ← hA, ← hB, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomm]
  have hboundary (a : β) : (Ideal.span {w a}).map φ = (Ideal.span {v a}).map ψ := by
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    rw [← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, ← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, hφ, hψ,
      ← hw a, ← hv a, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomm]
  have he := Modeled.LogarithmicNaturality.Construction.logarithmic_ideals_agree_on_common_etale_refinement φₖ ψₖ hφe hψe
    w v M N hboundary A B hAB n
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  change (Affine.QuotientKernel.Construction.affineQuotientKernel _).comap u = (Affine.QuotientKernel.Construction.affineQuotientKernel _).comap z
  rw [← hφ, ← hψ, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  exact congrArg Affine.QuotientKernel.Construction.affineQuotientKernel he

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.LogarithmicOverlap.Construction
