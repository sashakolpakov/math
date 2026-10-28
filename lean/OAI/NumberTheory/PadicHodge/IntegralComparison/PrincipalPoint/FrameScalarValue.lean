import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.FrameScalar

/-! # Frame Scalar Value -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.FrameScalarValue

noncomputable section

/-! A scalar defined using a section frame evaluates in that exact
module frame after passing to the intrinsic affine purity coordinate. -/
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

variable (eN : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(Y, U) Γ(Y, U))

theorem value_sectionFrame :
    FrameScalar.value U hU N M K ε I eM eI
      (Affine.LineFrameNormalization.PrincipalOrientedResidue.sectionFrame U hU N eN)
      s t hreg hI W d hL hzero y =
    eI ((Affine.OrientedPurity.iso U hU N K M ε I eM (Fin.append s t)
      ((KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t).trans hI) hreg eN).hom
        ((Principal.ProductPointCoordinates.sectionIso U hU N K (c+m)).inv
          (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (Principal.ProductPointScalar.principal U hU N K)) (c+m) y))) := by
  rw [FrameScalar.value_eq, Affine.LineFrameNormalization.PrincipalOrientedResidue.lineIso_sectionFrame]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.FrameScalarValue
