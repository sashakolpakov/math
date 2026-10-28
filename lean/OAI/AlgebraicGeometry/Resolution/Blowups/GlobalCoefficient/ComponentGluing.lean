import OAI.AlgebraicGeometry.Resolution.Blowups.Component.CenterOverlap
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenIdealSheafUniqueness
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealSheafIdentification
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealChartDescent

/-! # Component Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ComponentGluing.Construction

noncomputable section

/-! Native global component centers from independent smooth affine maximal-contact charts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem affineQuotientKernel_eq_iff {R : Type u} [CommRing R] (I J : Ideal R) :
    Affine.QuotientKernel.Construction.affineQuotientKernel I = Affine.QuotientKernel.Construction.affineQuotientKernel J ↔ I = J := by
  constructor
  · intro h
    exact le_antisymm ((Affine.IdealChartDescent.Construction.affineQuotientKernel_le_iff I J).mp h.le)
      ((Affine.IdealChartDescent.Construction.affineQuotientKernel_le_iff J I).mp h.ge)
  · exact congrArg Affine.QuotientKernel.Construction.affineQuotientKernel

theorem idealSheaf_eq_of_fromSpec {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : ∀ U : X.affineOpens, I.comap U.2.fromSpec = J.comap U.2.fromSpec) : I = J := by
  ext1
  funext U
  have he := h U
  rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel] at he
  exact (affineQuotientKernel_eq_iff (I.ideal U) (J.ideal U)).mp he

theorem existsUnique_global_coefficient_component_center
    (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {ι : Type v} [Finite ι]
    (R : ι → CommRingCat.{u}) [∀ i, Algebra k (R i)] [∀ i, Algebra ℚ (R i)]
    [∀ i, Algebra.Smooth k (R i)] (j : ∀ i, Spec (R i) ⟶ X)
    [∀ i, IsOpenImmersion (j i)] [∀ i, QuasiCompact (j i)]
    (hstructure : ∀ i, j i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (R i))))
    (hcover : ⨆ i, (j i).opensRange = ⊤) (J : X.IdealSheafData)
    (A : ∀ i, Ideal (R i)) (hA : ∀ i, J.comap (j i) = Affine.QuotientKernel.Construction.affineQuotientKernel (A i))
    (n : ℕ) (z : ∀ i, R i) (D : ∀ i, Derivation k (R i) (R i))
    (hD : ∀ i, D i (z i) = 1) (hz : ∀ i, z i ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (A i) n) :
    ∃! I : X.IdealSheafData, ∀ i, I.comap (j i) =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k (z i) (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (A i) n) (n + 1)) := by
  let C (i : ι) := Affine.QuotientKernel.Construction.affineQuotientKernel
    (Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k (z i) (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (A i) n) (n + 1))
  apply Blowups.Finite.OpenIdealSheafUniqueness.Construction.existsUnique_idealSheaf_of_finite_affine_cover (fun i => Spec (R i)) j hcover C
  intro a b
  apply idealSheaf_eq_of_fromSpec
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
    apply (affineQuotientKernel_eq_iff _ _).mp
    rw [← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, ← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, hφ, hψ,
      ← hA a, ← hA b, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomm]
  have hc := Component.CenterOverlap.Construction.coefficient_component_centers_agree_on_common_refinement k φₖ ψₖ hφe hψe
    (A a) (A b) hAJ n (z a) (z b) (D a) (D b) (hD a) (hD b) (hz a) (hz b)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  change (C a).comap u = (C b).comap v
  rw [← hφ, ← hψ]
  change (Affine.QuotientKernel.Construction.affineQuotientKernel _).comap _ = (Affine.QuotientKernel.Construction.affineQuotientKernel _).comap _
  rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  exact congrArg Affine.QuotientKernel.Construction.affineQuotientKernel hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ComponentGluing.Construction
