import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ComponentGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.TangentCenterChoice

/-! # Tangent Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.TangentGluing.Construction

noncomputable section

/-! Native finite-order surface coefficient centers glue at one common coefficient level. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem existsUnique_global_surface_tangent_center
    (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {ι : Type v} [Finite ι]
    (R : ι → CommRingCat.{u}) [∀ i, Algebra k (R i)] [∀ i, Algebra ℚ (R i)]
    [∀ i, Algebra.Smooth k (R i)] (j : ∀ i, Spec (R i) ⟶ X)
    [∀ i, IsOpenImmersion (j i)] [∀ i, QuasiCompact (j i)]
    (hstructure : ∀ i, j i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (R i))))
    (hcover : ⨆ i, (j i).opensRange = ⊤) (J : X.IdealSheafData)
    (A : ∀ i, Ideal (R i)) (hA : ∀ i, J.comap (j i) = Affine.QuotientKernel.Construction.affineQuotientKernel (A i))
    (n ℓ : ℕ) (C : ∀ i, Surface.TangentCenterChoice.Construction.SurfaceTangentCenterChoice k (R i) (A i) n ℓ)
    (hdim : ∀ i, ringKrullDim (R i) ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1) :
    ∃! I : X.IdealSheafData, ∀ i, I.comap (j i) = Affine.QuotientKernel.Construction.affineQuotientKernel (C i).center := by
  let K (i : ι) := Affine.QuotientKernel.Construction.affineQuotientKernel (C i).center
  apply Blowups.Finite.OpenIdealSheafUniqueness.Construction.existsUnique_idealSheaf_of_finite_affine_cover (fun i => Spec (R i)) j hcover K
  intro a b
  apply GlobalCoefficient.ComponentGluing.Construction.idealSheaf_eq_of_fromSpec
  intro W
  let P := pullback (j a) (j b)
  let S := Γ(P, W)
  let u : Spec (.of S) ⟶ Spec (R a) := W.2.fromSpec ≫ pullback.fst (j a) (j b)
  let v : Spec (.of S) ⟶ Spec (R b) := W.2.fromSpec ≫ pullback.snd (j a) (j b)
  let φ : R a →+* S := (Spec.preimage u).hom
  let ψ : R b →+* S := (Spec.preimage v).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = u := Spec.map_preimage u
  have hψ : Spec.map (CommRingCat.ofHom ψ) = v := Spec.map_preimage v
  have hcomm : u ≫ j a = v ≫ j b := by
    dsimp only [u, v]
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hbase : φ.comp (algebraMap k (R a)) = ψ.comp (algebraMap k (R b)) := by
    have he : CommRingCat.ofHom (φ.comp (algebraMap k (R a))) =
        CommRingCat.ofHom (ψ.comp (algebraMap k (R b))) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom (algebraMap k (R a)) ≫ CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap k (R b)) ≫ CommRingCat.ofHom ψ)
      rw [Spec.map_comp, Spec.map_comp, hφ, hψ, ← hstructure a, ← hstructure b]
      simpa only [Category.assoc] using congrArg (fun m => m ≫ f) hcomm
    exact congrArg CommRingCat.Hom.hom he
  let : Algebra k S := (φ.comp (algebraMap k (R a))).toAlgebra
  let φₖ : R a →ₐ[k] S := { __ := φ, commutes' := fun _ => rfl }
  let ψₖ : R b →ₐ[k] S := { __ := ψ, commutes' := fun c => (RingHom.congr_fun hbase c).symm }
  let : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  have hφe : φₖ.toRingHom.Etale := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    exact inferInstanceAs (Etale u)
  have hψe : ψₖ.toRingHom.Etale := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    exact inferInstanceAs (Etale v)
  have hAJ : (A a).map φ = (A b).map ψ := by
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    rw [← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, ← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, hφ, hψ,
      ← hA a, ← hA b, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomm]
  have hc := Surface.TangentCenterChoice.Construction.SurfaceTangentCenterChoice.center_eq_on_common_refinement φₖ ψₖ hφe hψe hAJ (C a) (C b) (hdim a) (hdim b) hlevel
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  change (K a).comap u = (K b).comap v
  rw [← hφ, ← hψ]
  change (Affine.QuotientKernel.Construction.affineQuotientKernel _).comap _ = (Affine.QuotientKernel.Construction.affineQuotientKernel _).comap _
  rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  exact congrArg Affine.QuotientKernel.Construction.affineQuotientKernel hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.TangentGluing.Construction
