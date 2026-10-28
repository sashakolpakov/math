import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDualPoints
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOverlap

/-! # Dual Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualOpen

noncomputable section

section

/-! The actual relative Spec equivalence identifies algebra dual-number
points with scheme dual-number points and preserves their reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints

variable {S : Type} [CommRing S] [Algebra ℂ S]

def affineDualSchemeMap (f : S →ₐ[ℂ] DualNumber ℂ) : LieRanks.dualNumberTest ℂ ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S :=
  Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S (DualNumber ℂ) f

theorem affineDualSchemeMap_reduction (f : S →ₐ[ℂ] DualNumber ℂ) :
    LieRanks.dualNumberOrigin ℂ ≫ affineDualSchemeMap f =
      Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv S ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp f) := by
  apply Over.OverMorphism.ext
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left]
  change Spec.map (CommRingCat.ofHom (LieRanks.dualNumberReduction ℂ)) ≫
    Spec.map (CommRingCat.ofHom f.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

def affineDualSchemeEquiv (x : S →ₐ[ℂ] ℂ) :
    Dual.PresentedAlgebra.DualAlgebraPoints x ≃ DualOpen.Lifts.DualSchemePoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S) (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv S x) where
  toFun f := ⟨affineDualSchemeMap f.val, (affineDualSchemeMap_reduction f.val).trans
    (congrArg (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv S) f.property)⟩
  invFun f := ⟨(Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S (DualNumber ℂ)).symm f.val, by
    apply (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv S).injective
    have hf : affineDualSchemeMap ((Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S (DualNumber ℂ)).symm f.val) = f.val :=
      (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S (DualNumber ℂ)).apply_symm_apply f.val
    exact (affineDualSchemeMap_reduction _).symm.trans
      ((congrArg (fun g => LieRanks.dualNumberOrigin ℂ ≫ g) hf).trans f.property)⟩
  left_inv f := Subtype.ext ((Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S (DualNumber ℂ)).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S (DualNumber ℂ)).apply_symm_apply f.val)

theorem affineDualSchemeMap_comp {T : Type} [CommRing T] [Algebra ℂ T]
    (h : S →ₐ[ℂ] T) (f : T →ₐ[ℂ] DualNumber ℂ) :
    affineDualSchemeMap (f.comp h) =
      affineDualSchemeMap f ≫ Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S T h := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (f.comp h).toRingHom) =
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom h.toRingHom)
  rw [← Spec.map_comp]
  rfl

end

section

/-! An actual affine open immersion transports the native tangent
comparison to scheme-valued dual-number points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential
open scoped _root_.Manifold ContDiff

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    (A : CommAlgCat ℂ) [IsDomain A] [Algebra.Smooth ℂ A]

local notation "ModelA" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)
local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

def affineOpenTangentDualEquiv (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    TangentSpace 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x) ≃
      DualOpen.Lifts.DualSchemePoints X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x) :=
  (LinearEquiv.ofBijective
    (mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x).toLinearMap
    (ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective A i x)).symm.toEquiv.trans
      ((Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv x).trans
        ((affineDualSchemeEquiv x).trans
          (DualOpen.Lifts.dualOpenPointsEquiv i (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A x))))

theorem affineOpenTangentDualEquiv_mfderiv (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (v : TangentSpace 𝓘(ℂ, ModelA) x) :
    (affineOpenTangentDualEquiv A i x
      (mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x v)).val =
        affineDualSchemeMap (Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv x v).val ≫ i := by
  let d := LinearEquiv.ofBijective
    (mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x).toLinearMap
    (ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective A i x)
  exact congrArg (fun w => affineDualSchemeMap (Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv x w).val ≫ i)
    (d.symm_apply_apply v)

end

section

/-! The actual tangent comparison commutes with a refinement of affine
open neighborhoods, by the chain rule and functoriality of relative Spec. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential
open scoped _root_.Manifold ContDiff

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    (A B : CommAlgCat ℂ) [IsDomain A] [Algebra.Smooth ℂ A]
    [IsDomain B] [Algebra.Smooth ℂ B]

local notation "ModelA" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)
local notation "ModelB" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ)
local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

theorem affinePointMap_refinement_derivative
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) (h : A →ₐ[ℂ] B)
    (hfac : Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B h ≫ i = j)
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (v : TangentSpace 𝓘(ℂ, ModelB) y) :
    mfderiv 𝓘(ℂ, ModelB) 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j) y v =
      mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i)
        (y.comp h) (mfderiv 𝓘(ℂ, ModelB) 𝓘(ℂ, ModelA)
          (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) y v) := by
  have heq : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i ∘ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h := by
    funext z
    rw [← hfac, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap]
    rfl
  rw [heq]
  exact mfderiv_comp_apply y
    ((ComplexPoints.Analytic.AffineOpenDifferential.contMDiff_affinePointMap A i 1).mdifferentiableAt one_ne_zero)
    ((ComplexPoints.Analytic.SmoothAffineMaps.contMDiff_smoothDomain_comap h 1).mdifferentiableAt one_ne_zero) v

theorem affineOpenTangentDual_refinement
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion j.left]
    (h : A →ₐ[ℂ] B) (hfac : Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B h ≫ i = j)
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (v : ModelX) :
    (affineOpenTangentDualEquiv A i (y.comp h) v).val =
      (affineOpenTangentDualEquiv B j y v).val := by
  obtain ⟨w, rfl⟩ := (ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective B j y).surjective v
  have hd := affinePointMap_refinement_derivative A B i j h hfac y w
  have hleft := congrArg (fun z : ModelX =>
    (affineOpenTangentDualEquiv A i (y.comp h) z).val) hd
  have ha := affineOpenTangentDualEquiv_mfderiv A i (y.comp h)
    (mfderiv 𝓘(ℂ, ModelB) 𝓘(ℂ, ModelA) (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) y w)
  have hn := congrArg (fun f : A →ₐ[ℂ] DualNumber ℂ => affineDualSchemeMap f ≫ i)
    (Intrinsic.AffineDualPoints.nativeAffineDualPoint_natural h y w)
  have hc : affineDualSchemeMap ((Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv y w).val.comp h) ≫ i =
      affineDualSchemeMap (Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv y w).val ≫ j := by
    rw [affineDualSchemeMap_comp, Category.assoc, hfac]
  exact hleft.trans (ha.trans (hn.trans (hc.trans
    (affineOpenTangentDualEquiv_mfderiv B j y w).symm)))

end

/-! Independence of the actual tangent comparison from its affine open
neighborhood, proved on a common principal localization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential
open scoped _root_.Manifold ContDiff

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    (A B : CommAlgCat ℂ) [IsDomain A] [Algebra.Smooth ℂ A]
    [IsDomain B] [Algebra.Smooth ℂ B]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

theorem affineOpenTangentDual_independent
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion j.left]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)
    (hxy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j y)
    (v : ModelX) :
    (affineOpenTangentDualEquiv A i x v).val =
      (affineOpenTangentDualEquiv B j y v).val := by
  obtain ⟨a, ha, h, hfac, hpoint⟩ :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineLocalizationTransition A B i j x ⟨y, hxy.symm⟩
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
  have hzA : z.comp r = x := Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x a ha
  have hzB : z.comp h = y :=
    (ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap B j).injective ((hpoint ⟨x, ha⟩).trans hxy)
  have hA := affineOpenTangentDual_refinement A C i k r rfl z v
  have hB := affineOpenTangentDual_refinement B C j k h hfac z v
  have hAx : (affineOpenTangentDualEquiv A i (z.comp r) v).val =
      (affineOpenTangentDualEquiv A i x v).val :=
    congrArg (fun q => (affineOpenTangentDualEquiv A i q v).val) hzA
  have hBy : (affineOpenTangentDualEquiv B j (z.comp h) v).val =
      (affineOpenTangentDualEquiv B j y v).val :=
    congrArg (fun q => (affineOpenTangentDualEquiv B j q v).val) hzB
  exact hAx.symm.trans (hA.trans (hB.symm.trans hBy))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualOpen
