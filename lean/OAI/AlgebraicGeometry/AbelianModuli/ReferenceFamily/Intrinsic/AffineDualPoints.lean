import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.IntrinsicAffineTangent
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineMaps

/-! # Affine Dual Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDualPoints

noncomputable section

/-! Native affine tangent vectors are actual dual-number points, with
scalar compatibility and functoriality for genuine algebra maps. -/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineMaps
open scoped _root_.Manifold ContDiff

variable {S : Type*} [CommRing S] [Algebra ℂ S] [IsDomain S] [Algebra.Smooth ℂ S]
local notation "ModelS" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ S) → ℂ)

def nativeAffineDualPointEquiv (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) :
    TangentSpace 𝓘(ℂ, ModelS) x ≃ Dual.PresentedAlgebra.DualAlgebraPoints x :=
  (Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations x).toEquiv.trans (PointDerivations.dualPointDerivationsEquiv x).symm

theorem nativeAffineDualPoint_fst (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S)
    (v : TangentSpace 𝓘(ℂ, ModelS) x) (a : S) :
    ((nativeAffineDualPointEquiv x v).val a).fst = x a :=
  DFunLike.congr_fun (nativeAffineDualPointEquiv x v).property a

theorem nativeAffineDualPoint_snd (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S)
    (v : TangentSpace 𝓘(ℂ, ModelS) x) (a : S) :
    ((nativeAffineDualPointEquiv x v).val a).snd =
      mfderiv 𝓘(ℂ, ModelS) 𝓘(ℂ, ℂ) (fun y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S => y a) x v :=
  Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations_apply x v a

theorem nativeAffineDualPoint_scale (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S)
    (v : TangentSpace 𝓘(ℂ, ModelS) x) (z : ℂ) :
    (LieRanks.dualNumberScale ℂ z).comp (nativeAffineDualPointEquiv x v).val =
      (nativeAffineDualPointEquiv x (z • v)).val := by
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · exact (TrivSqZeroExt.fst_map (z • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
      ((nativeAffineDualPointEquiv x v).val a)).trans
        ((nativeAffineDualPoint_fst x v a).trans (nativeAffineDualPoint_fst x (z • v) a).symm)
  · have h := TrivSqZeroExt.snd_map (z • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
      ((nativeAffineDualPointEquiv x v).val a)
    change ((LieRanks.dualNumberScale ℂ z) ((nativeAffineDualPointEquiv x v).val a)).snd = _
    refine h.trans ?_
    change z • (Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations x v).val a =
      (Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations x (z • v)).val a
    exact (congrArg (fun D : PointDerivations.pointDerivations x => D.val a)
      ((Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations x).map_smul z v)).symm

variable {T : Type*} [CommRing T] [Algebra ℂ T] [IsDomain T] [Algebra.Smooth ℂ T]
local notation "ModelT" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ T) → ℂ)

theorem nativeAffineTangentDerivations_natural (h : S →ₐ[ℂ] T)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints T) (v : TangentSpace 𝓘(ℂ, ModelT) x) (a : S) :
    (Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations (x.comp h)
      (mfderiv 𝓘(ℂ, ModelT) 𝓘(ℂ, ModelS) (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) x v)).val a =
      (Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations x v).val (h a) := by
  have hf := (ComplexPoints.Analytic.SmoothAffineMaps.contMDiff_smoothDomain_comap h 1).mdifferentiableAt (x := x) one_ne_zero
  have hg := (Regular.IntrinsicAffineTangent.contMDiff_affineEvaluation a 1).mdifferentiableAt (x := x.comp h) one_ne_zero
  have hc := mfderiv_comp_apply (I := 𝓘(ℂ, ModelT)) (I' := 𝓘(ℂ, ModelS))
    (I'' := 𝓘(ℂ, ℂ)) x hg hf v
  exact (Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations_apply (x.comp h) _ a).trans
    (hc.symm.trans (Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations_apply x v (h a)).symm)

theorem nativeAffineDualPoint_natural (h : S →ₐ[ℂ] T)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints T) (v : TangentSpace 𝓘(ℂ, ModelT) x) :
    (nativeAffineDualPointEquiv (x.comp h)
      (mfderiv 𝓘(ℂ, ModelT) 𝓘(ℂ, ModelS) (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) x v)).val =
      (nativeAffineDualPointEquiv x v).val.comp h := by
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · exact (nativeAffineDualPoint_fst (x.comp h) _ a).trans (nativeAffineDualPoint_fst x v (h a)).symm
  · exact nativeAffineTangentDerivations_natural h x v a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDualPoints
