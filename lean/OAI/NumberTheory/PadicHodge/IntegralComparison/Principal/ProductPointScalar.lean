import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ProductPointCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrientedPurityTransport

/-! # Product Point Scalar -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ProductPointScalar

noncomputable section

/-! The scalar of the actual supported product-point class is the
original affine purity coefficient in a fixed quotient, evaluated at
the section. All equation-ideal transports are explicit. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem quotient_chain (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    {I J L : Ideal A} (hIJ : I = J) (hJL : J = L) (x : A ⧸ I) :
    Ideal.quotientEquivAlgOfEq k (hIJ.trans hJL) x =
      Ideal.quotientEquivAlgOfEq k hJL (Submodule.quotEquivOfEq I J hIJ x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

private theorem quotient_roundtrip (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    {I J : Ideal A} (h : I = J) (x : A ⧸ J) :
    Ideal.quotientEquivAlgOfEq k h (Ideal.quotientEquivAlgOfEq A h.symm x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Koszul.Comparison OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ProductPointCoordinates
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (M : Y.Modules) [M.IsQuasicoherent]
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  [∀ q, ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]
  (J : Ideal Γ(Y, U))
  (eMJ : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ J))
  {c m : ℕ} (s : Fin c → Γ(Y, U)) (t : Fin m → Γ(Y, U))
  (hst : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn (Fin.append s t)))
  (hJ : KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t = J)
  {k : Type u} [CommRing k] [Algebra k Γ(Y, U)]
  (eJ : (Γ(Y, U) ⧸ J) ≃ₐ[k] k)

abbrev principal := Koszul.Comparison.nativeComplex U hU N K

variable (W : ULift.{u} (Fin m) → SectionPresheaf.Index U)
  (d : ℕ) (hL : ∀ q, q ≠ d → (principal U hU N K).ExactAt q)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
    IsZero ((((single ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Y, U))
      (.up ℕ) d).obj ((principal U hU N K).homology d)).X p).obj
        (op ((AugmentedOrdered.Cech.formal W q).obj a))))
  (y : ((AugmentedOrdered.CechFunctor.bicomplex W (principal U hU N K)).total (.up ℕ)).homology (c+m))

 theorem normalization :
    KoszulPoint.ScalarCoordinates.scalar k Γ(Y, U) (SectionPresheaf.rings U hU)
      (TerminalScalars.bijective U hU) W s t
      (PrincipalPoint.Koszul.Comparison.productCoordinates U hU N e M K ε s t hst
        (eMJ ≪≫ (Ideal.quotientEquivAlgOfEq Γ(Y, U) hJ.symm).toLinearEquiv.toModuleIso))
      d hL hzero
      ((Ideal.quotientEquivAlgOfEq k
        ((KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t).trans hJ)).trans eJ) y =
    eJ ((Affine.OrientedPurity.iso U hU N K M ε J eMJ (Fin.append s t)
      ((KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t).trans hJ) hst
      (OrientedResidueNormalizationBase.lineIso U hU N e)).hom
        ((ProductPointCoordinates.sectionIso U hU N K (c+m)).inv
          (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (principal U hU N K)) (c+m) y))) := by
  let eMP := eMJ ≪≫ (Ideal.quotientEquivAlgOfEq Γ(Y, U) hJ.symm).toLinearEquiv.toModuleIso
  let v := homologyMap (AugmentedOrdered.CechForget.forgetSupport W (principal U hU N K)) (c+m) y
  let w := (ProductPointCoordinates.sectionIso U hU N K (c+m)).inv v
  have hc := ConcreteCategory.congr_hom (ProductPointCoordinates.coordinateMap_eq U hU N e M K ε s t hst eMP) v
  change ProductPointCoordinates.coordinateMap U hU N e M K ε s t hst eMP v =
    (Affine.OrientedPurity.iso U hU N K M ε
      (KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t) eMP (Fin.append s t)
      (KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t) hst
      (OrientedResidueNormalizationBase.lineIso U hU N e)).hom w at hc
  have hi := Affine.OrientedPurityTransport.iso_cast U hU N K M ε J
    (KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t) hJ.symm eMJ (Fin.append s t)
    ((KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t).trans hJ) hst
    (OrientedResidueNormalizationBase.lineIso U hU N e)
  have hp := congrArg (fun E => E.hom w) hi
  change (Affine.OrientedPurity.iso U hU N K M ε
      (KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t) eMP (Fin.append s t)
      (KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t) hst
      (OrientedResidueNormalizationBase.lineIso U hU N e)).hom w =
    Ideal.quotientEquivAlgOfEq Γ(Y, U) hJ.symm
      ((Affine.OrientedPurity.iso U hU N K M ε J eMJ (Fin.append s t)
        ((KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t).trans hJ) hst
        (OrientedResidueNormalizationBase.lineIso U hU N e)).hom w) at hp
  rw [KoszulPoint.ScalarAmbient.scalar]
  change eJ (Ideal.quotientEquivAlgOfEq k
    ((KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t).trans hJ)
      (KoszulPoint.ScalarAmbient.coordinate Γ(Y, U) (SectionPresheaf.rings U hU)
        (TerminalScalars.bijective U hU) (Fin.append s t)
        (PrincipalPoint.Koszul.Comparison.productCoordinates U hU N e M K ε s t hst eMP) v)) = _
  rw [quotient_chain k Γ(Y, U)
    (KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t) hJ]
  change eJ (Ideal.quotientEquivAlgOfEq k hJ
    (ProductPointCoordinates.coordinateMap U hU N e M K ε s t hst eMP v)) = _
  rw [hc, hp, quotient_roundtrip]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ProductPointScalar
