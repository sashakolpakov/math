import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent

/-! # Scheme Dual Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualNaturality

noncomputable section

section

/-! Functoriality of the canonical tangent comparison for a genuine
scheme map described on source and target affine neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [Smooth Y.hom]
    (A B : CommAlgCat ℂ) [IsDomain A] [Algebra.Smooth ℂ A]
    [IsDomain B] [Algebra.Smooth ℂ B]

local notation "ModelA" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)
local notation "ModelB" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ)
local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

theorem schemeMap_affine_derivative (φ : X ⟶ Y)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y) [IsOpenImmersion j.left]
    (h : B →ₐ[ℂ] A) (hfac : Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B A h ≫ j = i ≫ φ)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (v : TangentSpace 𝓘(ℂ, ModelA) x) :
    mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x)
      (mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x v) =
    mfderiv 𝓘(ℂ, ModelB) 𝓘(ℂ, ModelY) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j)
      (x.comp h) (mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelB) (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) x v) := by
  have hc := mfderiv_comp_apply (I := 𝓘(ℂ, ModelA)) (I' := 𝓘(ℂ, ModelX))
    (I'' := 𝓘(ℂ, ModelY)) x
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ 1).mdifferentiableAt one_ne_zero)
    ((ComplexPoints.Analytic.AffineOpenDifferential.contMDiff_affinePointMap A i 1).mdifferentiableAt one_ne_zero) v
  have heq : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A (i ≫ φ) := by
    funext z
    exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp A i φ z).symm
  have ht := congrArg (fun f : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y =>
    mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelY) f x v) heq
  exact hc.symm.trans (ht.trans
    (Affine.DualOpen.affinePointMap_refinement_derivative B A j (i ≫ φ) h hfac x v))

theorem nativeSchemeTangentDual_natural_on_affine (φ : X ⟶ Y)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y) [IsOpenImmersion j.left]
    (h : B →ₐ[ℂ] A) (hfac : Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B A h ≫ j = i ≫ φ)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (v : ModelX) :
    (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv Y
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x))
      (mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x) v)).val =
      (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x) v).val ≫ φ := by
  obtain ⟨w, rfl⟩ := (ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective A i x).surjective v
  have hp : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j (x.comp h) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x) := by
    calc
      _ = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B A h ≫ j) x :=
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap B A h j x).symm
      _ = _ := by rw [hfac, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp]
  have hchart := Intrinsic.SchemeDualTangent.nativeSchemeTangentDual_affine Y _ B j (x.comp h) hp
    (mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x)
      (mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x w))
  have hd := congrArg (fun z : ModelY => (Affine.DualOpen.affineOpenTangentDualEquiv B j (x.comp h) z).val)
    (schemeMap_affine_derivative A B φ i j h hfac x w)
  have hj := Affine.DualOpen.affineOpenTangentDualEquiv_mfderiv B j (x.comp h)
    (mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelB) (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) x w)
  have hn := congrArg (fun f : B →ₐ[ℂ] DualNumber ℂ => Affine.DualOpen.affineDualSchemeMap f ≫ j)
    (Intrinsic.AffineDualPoints.nativeAffineDualPoint_natural h x w)
  have hspec : Affine.DualOpen.affineDualSchemeMap ((Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv x w).val.comp h) ≫ j =
      (Affine.DualOpen.affineDualSchemeMap (Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv x w).val ≫ i) ≫ φ := by
    rw [Affine.DualOpen.affineDualSchemeMap_comp, Category.assoc, hfac, Category.assoc]
  have hi := congrArg (fun f : LieRanks.dualNumberTest ℂ ⟶ X => f ≫ φ)
    (Intrinsic.SchemeDualTangent.nativeSchemeTangentDual_mfderiv X A i x w)
  exact hchart.trans (hd.trans (hj.trans (hn.trans (hspec.trans hi.symm))))

end

section

/-! The canonical comparison between actual dual-number points and
native analytic tangents is natural for every morphism of smooth
integral complex schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

theorem exists_smoothAffineOpenPoint_lift (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral X.left] [Smooth X.hom] (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ∃ (A : CommAlgCat ℂ) (_ : IsDomain A) (_ : Algebra.Smooth ℂ A)
      (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (_ : IsOpenImmersion i.left)
      (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A), ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x = p := by
  obtain ⟨U, hU, x, hx⟩ := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift X p
  have hpU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p ∈ U := by
    have hr : p ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) := ⟨x, hx⟩
    rwa [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hr
  let : Nonempty U := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p, hpU⟩⟩
  exact ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U,
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain X U,
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X U hU,
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU, inferInstance, x, hx⟩

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [Smooth Y.hom]
local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

theorem nativeSchemeTangentDual_natural (φ : X ⟶ Y) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (v : TangentSpace 𝓘(ℂ, ModelX) p) :
    (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ p)
      (mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) p v)).val =
      (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X p v).val ≫ φ := by
  obtain ⟨A, hAd, hAs, i, hi, x, hx⟩ := exists_smoothAffineOpenPoint_lift X p
  let : IsDomain A := hAd
  let : Algebra.Smooth ℂ A := hAs
  let : IsOpenImmersion i.left := hi
  obtain ⟨B, hBd, hBs, j, hj, y, hy⟩ :=
    exists_smoothAffineOpenPoint_lift Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ p)
  let : IsDomain B := hBd
  let : Algebra.Smooth ℂ B := hBs
  let : IsOpenImmersion j.left := hj
  have hr : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A (i ≫ φ) x ∈
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j) := by
    refine ⟨y, ?_⟩
    exact hy.trans ((congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) hx).symm.trans
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp A i φ x).symm)
  obtain ⟨a, ha, h, hfac, _⟩ :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineLocalizationTransition A B (i ≫ φ) j x hr
  have hane : a ≠ 0 := fun heq => ha (heq ▸ map_zero x)
  let C := CommAlgCat.of ℂ (Localization.Away a)
  let : IsDomain C := Localization.Away.isDomain hane
  let : Algebra.Smooth A C := Algebra.Smooth.of_isLocalization_Away a
  let : Algebra.Smooth ℂ C := Algebra.Smooth.comp ℂ A C
  let r : A →ₐ[ℂ] C := Algebra.algHom ℂ A (Localization.Away a)
  let k := Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C r ≫ i
  let : IsOpenImmersion (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C r).left := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))))
    infer_instance
  let : IsOpenImmersion k.left := by
    change IsOpenImmersion ((Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C r).left ≫ i.left)
    infer_instance
  let z : Foundations.Scheme.AffineComplexPoints.affineComplexPoints C := Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x a ha
  have hz : z.comp r = x := Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x a ha
  have hk : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap C k z = p :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap A C r i z).trans
      ((congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) hz).trans hx)
  have hf : Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B C h ≫ j = k ≫ φ :=
    hfac.trans (Category.assoc _ i φ).symm
  have hn := nativeSchemeTangentDual_natural_on_affine C B φ k j h hf z v
  exact hk ▸ hn

end

/-! Complex scalar multiplication in the native analytic tangent space
is the intrinsic precomposition action of dual-number scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

theorem affineDualSchemeMap_scale {S : Type} [CommRing S] [Algebra ℂ S]
    (f : S →ₐ[ℂ] DualNumber ℂ) (a : ℂ) :
    Affine.DualOpen.affineDualSchemeMap ((LieRanks.dualNumberScale ℂ a).comp f) =
      LieRanks.dualNumberScalar ℂ a ≫ Affine.DualOpen.affineDualSchemeMap f := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((LieRanks.dualNumberScale ℂ a).comp f).toRingHom) =
    Spec.map (CommRingCat.ofHom (LieRanks.dualNumberScale ℂ a).toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom)
  rw [← Spec.map_comp]
  rfl

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

theorem nativeSchemeTangentDual_scale (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (a : ℂ)
    (v : TangentSpace 𝓘(ℂ, ModelX) p) :
    (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X p (a • v)).val =
      LieRanks.dualNumberScalar ℂ a ≫ (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X p v).val := by
  obtain ⟨A, hAd, hAs, i, hi, x, hx⟩ := exists_smoothAffineOpenPoint_lift X p
  let : IsDomain A := hAd
  let : Algebra.Smooth ℂ A := hAs
  let : IsOpenImmersion i.left := hi
  let D := mfderiv 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) 𝓘(ℂ, ModelX)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x
  obtain ⟨w, hw⟩ := (ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective A i x).surjective v
  have hscale : a • v = D (a • w) :=
    (congrArg (fun z : ModelX => a • z) hw).symm.trans (D.map_smul a w).symm
  have hleft := (Intrinsic.SchemeDualTangent.nativeSchemeTangentDual_affine X p A i x hx (a • v)).trans
    ((congrArg (fun z : ModelX => (Affine.DualOpen.affineOpenTangentDualEquiv A i x z).val) hscale).trans
      (Affine.DualOpen.affineOpenTangentDualEquiv_mfderiv A i x (a • w)))
  have hright : (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X p v).val =
      Affine.DualOpen.affineDualSchemeMap (Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv x w).val ≫ i :=
    (Intrinsic.SchemeDualTangent.nativeSchemeTangentDual_affine X p A i x hx v).trans
      ((congrArg (fun z : ModelX => (Affine.DualOpen.affineOpenTangentDualEquiv A i x z).val) hw.symm).trans
        (Affine.DualOpen.affineOpenTangentDualEquiv_mfderiv A i x w))
  have hn := congrArg (fun f : A →ₐ[ℂ] DualNumber ℂ => Affine.DualOpen.affineDualSchemeMap f ≫ i)
    (Intrinsic.AffineDualPoints.nativeAffineDualPoint_scale x w a).symm
  have hs : Affine.DualOpen.affineDualSchemeMap ((LieRanks.dualNumberScale ℂ a).comp
      (Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv x w).val) ≫ i =
      LieRanks.dualNumberScalar ℂ a ≫ (Affine.DualOpen.affineDualSchemeMap (Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv x w).val ≫ i) := by
    rw [affineDualSchemeMap_scale, Category.assoc]
  exact hleft.trans (hn.trans (hs.trans
    (congrArg (fun f => LieRanks.dualNumberScalar ℂ a ≫ f) hright).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualNaturality
