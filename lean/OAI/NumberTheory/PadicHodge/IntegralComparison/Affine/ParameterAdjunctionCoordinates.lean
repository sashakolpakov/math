import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ParameterAdjunction

/-! # Parameter Adjunction Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ParameterAdjunctionCoordinates

noncomputable section

/-! The parameter-symbol formula applies directly to an equal original
ambient adjunction map, before any native geometric specialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.Module
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) (K : ChainComplex Y.Modules ℕ)
  [∀ q, (K.X q).IsQuasicoherent]
  (M : Y.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  (I : Ideal Γ(Y, U))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ I))
  [∀ q, ((LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]
  (eN : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(Y, U) Γ(Y, U))
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = I)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  (bI : Basis (Fin c) (Γ(Y, U) ⧸ I) I.Cotangent)
  (hI : ∀ i, bI i = I.toCotangent (ConormalKoszulPurity.conormalVectors Γ(Y, U) I s hs i))
  {k : Type u} [CommRing k] [Algebra k Γ(Y, U)]
  [Algebra.Smooth k Γ(Y, U)] [Algebra.Smooth k (Γ(Y, U) ⧸ I)]
  {g : ℕ} (bQ : Basis (Fin g) (Γ(Y, U) ⧸ I) Ω[Γ(Y, U) ⧸ I⁄k])
  (t : Fin g → Γ(Y, U))
  (ht : ∀ i, bQ i = KaehlerDifferential.D k (Γ(Y, U) ⧸ I) (Ideal.Quotient.mk I (t i)))
  (b : Basis (Fin (c + g)) Γ(Y, U) Ω[Γ(Y, U)⁄k])
  (hb : (b : Fin (c + g) → Ω[Γ(Y, U)⁄k]) =
    Fin.append (fun i => KaehlerDifferential.D k Γ(Y, U) (s i))
      (fun i => KaehlerDifferential.D k Γ(Y, U) (t i)))
  (e : (AffineOpen.InternalHom.sections U hU).obj N ≃ₗ[Γ(Y, U)] ⋀[Γ(Y, U)]^(c + g) Ω[Γ(Y, U)⁄k])
  (eA : ((Γ(Y, U) ⧸ I) ⊗[Γ(Y, U)] (AffineOpen.InternalHom.sections U hU).obj N) ≃ₗ[Γ(Y, U) ⧸ I]
    ⋀[Γ(Y, U) ⧸ I]^(c + g) ((Γ(Y, U) ⧸ I) ⊗[Γ(Y, U)] Ω[Γ(Y, U)⁄k]))
  (he : eA = ParameterLineAdjunction.ambient I b ((AffineOpen.InternalHom.sections U hU).obj N) e)

include hI ht hb he in
theorem symbol_with_ambient (x : (ModuleExactSections.sections U).obj
    ((LinearResolutionPurity.internalComplex N K).homology c)) :
    (DualizingAdjunction.iso U hU N K M ε I eM eN s hs hreg bI bQ eA).hom x =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior k (Γ(Y, U) ⧸ I) g
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol k (Γ(Y, U) ⧸ I)
        ((OrientedPurity.iso U hU N K M ε I eM s hs hreg
          (ParameterLineAdjunction.frame b ((AffineOpen.InternalHom.sections U hU).obj N) e)).hom x)
        (fun i => Ideal.Quotient.mk I (t i))) := by
  rw [he]
  exact ParameterAdjunction.symbol U hU N K M ε I eM eN s hs hreg bI hI bQ t ht b hb e x

include hI ht hb he in
theorem symbol_with_ambient_postcompose (Z : ModuleCat.{u} Γ(Y, U))
    (f : ModuleCat.of Γ(Y, U) (⋀[Γ(Y, U) ⧸ I]^g Ω[Γ(Y, U) ⧸ I⁄k]) ⟶ Z)
    (x : (ModuleExactSections.sections U).obj
      ((LinearResolutionPurity.internalComplex N K).homology c)) :
    ((DualizingAdjunction.iso U hU N K M ε I eM eN s hs hreg bI bQ eA).hom ≫ f) x =
    f (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior k (Γ(Y, U) ⧸ I) g
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol k (Γ(Y, U) ⧸ I)
        ((OrientedPurity.iso U hU N K M ε I eM s hs hreg
          (ParameterLineAdjunction.frame b ((AffineOpen.InternalHom.sections U hU).obj N) e)).hom x)
        (fun i => Ideal.Quotient.mk I (t i)))) := by
  have result := congrArg (fun v => f v)
    (symbol_with_ambient U hU N K M ε I eM eN s hs hreg bI hI bQ t ht b hb e eA he x)
  exact result

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ParameterAdjunctionCoordinates
