import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ProductPointScalar
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.PointFrameDimension
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LineFrameNormalization

/-! # Frame Scalar -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.FrameScalar

noncomputable section

/-! The actual product-point scalar is unchanged by replacing the full
regular equations and their differential frame. Its only class input is
the ambient image of the original supported class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Koszul.Comparison OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ProductPointCoordinates
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ProductPointScalar
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (M : Y.Modules) [M.IsQuasicoherent]
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  [∀ q, ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]
  (I : Ideal Γ(Y, U))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ I))
  {k : Type u} [CommRing k] [Algebra k Γ(Y, U)] (eI : (Γ(Y, U) ⧸ I) ≃ₐ[k] k)
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  {c m : ℕ} (s : Fin c → Γ(Y, U)) (t : Fin m → Γ(Y, U))
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn (Fin.append s t)))
  (hI : KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t = I)
  (W : ULift.{u} (Fin m) → Principal.SectionPresheaf.Index U)
  (d : ℕ) (hL : ∀ q, q ≠ d → (Principal.ProductPointScalar.principal U hU N K).ExactAt q)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
    IsZero ((((single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Y, U))
      (.up ℕ) d).obj ((Principal.ProductPointScalar.principal U hU N K).homology d)).X p).obj
        (op ((AugmentedOrdered.Cech.formal W q).obj a))))
  (y : ((AugmentedOrdered.CechFunctor.bicomplex W (Principal.ProductPointScalar.principal U hU N K)).total (.up ℕ)).homology (c+m))

def value : k :=
  KoszulPoint.ScalarCoordinates.scalar k Γ(Y, U) (Principal.SectionPresheaf.rings U hU)
    (Principal.TerminalScalars.bijective U hU) W s t
    (Koszul.Comparison.productCoordinates U hU N e M K ε s t hreg
      (eM ≪≫ (Ideal.quotientEquivAlgOfEq Γ(Y, U) hI.symm).toLinearEquiv.toModuleIso))
    d hL hzero
    ((Ideal.quotientEquivAlgOfEq k
      ((KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t).trans hI)).trans eI) y

theorem value_eq : value U hU N M K ε I eM eI e s t hreg hI W d hL hzero y =
    eI ((Affine.OrientedPurity.iso U hU N K M ε I eM (Fin.append s t)
      ((KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t).trans hI) hreg
      (Principal.OrientedResidueNormalizationBase.lineIso U hU N e)).hom
        ((Principal.ProductPointCoordinates.sectionIso U hU N K (c+m)).inv
          (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (Principal.ProductPointScalar.principal U hU N K)) (c+m) y))) :=
  Principal.ProductPointScalar.normalization U hU N e M K ε I eM s t hreg hI eI
    W d hL hzero y

variable [Algebra.Smooth k Γ(Y, U)] (h : c+m=d)
  (b : Module.Basis (Fin d) Γ(Y, U) Ω[Γ(Y, U)⁄k])
  (hb : (fun i : Fin (c+m) => b (Fin.cast h i)) =
    fun i => KaehlerDifferential.D k Γ(Y, U) (Fin.append s t i))
  (s' : Fin c → Γ(Y, U)) (t' : Fin m → Γ(Y, U))
  (hreg' : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn (Fin.append s' t')))
  (hI' : KoszulPartial.Resolution.pointIdeal Γ(Y, U) s' t' = I)
  (bt : Module.Basis (Fin d) Γ(Y, U) Ω[Γ(Y, U)⁄k])
  (hbt : (fun i : Fin (c+m) => bt (Fin.cast h i)) =
    fun i => KaehlerDifferential.D k Γ(Y, U) (Fin.append s' t' i))
  (eTop : (AffineOpen.InternalHom.sections U hU).obj N ≃ₗ[Γ(Y, U)] ⋀[Γ(Y, U)]^d Ω[Γ(Y, U)⁄k])
  (W' : ULift.{u} (Fin m) → Principal.SectionPresheaf.Index U)
  (hzero' : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
    IsZero ((((single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Y, U))
      (.up ℕ) d).obj ((Principal.ProductPointScalar.principal U hU N K).homology d)).X p).obj
        (op ((AugmentedOrdered.Cech.formal W' q).obj a))))
  (y' : ((AugmentedOrdered.CechFunctor.bicomplex W' (Principal.ProductPointScalar.principal U hU N K)).total (.up ℕ)).homology (c+m))
  (hxy : homologyMap (AugmentedOrdered.CechForget.forgetSupport W (Principal.ProductPointScalar.principal U hU N K)) (c+m) y =
    homologyMap (AugmentedOrdered.CechForget.forgetSupport W' (Principal.ProductPointScalar.principal U hU N K)) (c+m) y')

include h hb hbt hxy in
theorem independent :
    value U hU N M K ε I eM eI
      (Affine.LineFrameNormalization.PrincipalOrientedResidue.sectionFrame U hU N
        (ParameterLineAdjunction.frame (c := d) (g := 0) b ((AffineOpen.InternalHom.sections U hU).obj N) eTop))
      s t hreg hI W d hL hzero y =
    value U hU N M K ε I eM eI
      (Affine.LineFrameNormalization.PrincipalOrientedResidue.sectionFrame U hU N
        (ParameterLineAdjunction.frame (c := d) (g := 0) bt ((AffineOpen.InternalHom.sections U hU).obj N) eTop))
      s' t' hreg' hI' W' d hL hzero' y' := by
  simp only [value_eq, Affine.LineFrameNormalization.PrincipalOrientedResidue.lineIso_sectionFrame]
  rw [hxy]
  have hi := Affine.PointFrameDimension.independent U hU N K M ε I eM eI h
    (Fin.append s t) ((KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t).trans hI)
    hreg b hb
    (Fin.append s' t') ((KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s' t').trans hI')
    hreg' bt hbt eTop
  exact congrArg (fun a => eI (a ((Principal.ProductPointCoordinates.sectionIso U hU N K (c+m)).inv
    (homologyMap (AugmentedOrdered.CechForget.forgetSupport W' (Principal.ProductPointScalar.principal U hU N K)) (c+m) y')))) hi

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.FrameScalar
