import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.DualizingAdjunction

/-! # Adjunction Independence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.AdjunctionIndependence

noncomputable section

/-! The affine adjunction map is unchanged when all auxiliary frames,
equations, and quotient bases are changed together. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.DualizingAdjunction

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (K : ChainComplex X.Modules ℕ)
  [∀ q, (K.X q).IsQuasicoherent]
  (M : X.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  (I : Ideal Γ(X, U))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(X, U) (Γ(X, U) ⧸ I))
  [∀ q, ((LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]
  (eN eN' : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))
  {c : ℕ} (s : Fin c → Γ(X, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(X, U) s = I)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn s))
  (b : Module.Basis (Fin c) (Γ(X, U) ⧸ I) I.Cotangent)
  (hb : ∀ i, b i = I.toCotangent (ConormalKoszulPurity.conormalVectors Γ(X, U) I s hs i))
  (t : Fin c → Γ(X, U))
  (ht : Koszul.OrientedTopCohomology.ideal Γ(X, U) t = I)
  (htreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn t))
  (bt : Module.Basis (Fin c) (Γ(X, U) ⧸ I) I.Cotangent)
  (hbt : ∀ i, bt i = I.toCotangent (ConormalKoszulPurity.conormalVectors Γ(X, U) I t ht i))
  {k : Type u} [CommRing k] [Algebra k Γ(X, U)]
  [Algebra.Smooth k Γ(X, U)] [Algebra.Smooth k (Γ(X, U) ⧸ I)]
  {g : ℕ} (bQ bQ' : Module.Basis (Fin g) (Γ(X, U) ⧸ I) Ω[Γ(X, U) ⧸ I⁄k])
  (eAmbient eAmbient' : ((Γ(X, U) ⧸ I) ⊗[Γ(X, U)] (AffineOpen.InternalHom.sections U hU).obj N) ≃ₗ[Γ(X, U) ⧸ I]
    ⋀[Γ(X, U) ⧸ I]^(c + g) ((Γ(X, U) ⧸ I) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄k]))

include hb hbt in
theorem independent (he : eAmbient = eAmbient') :
    DualizingAdjunction.iso U hU N K M ε I eM eN s hs hreg b bQ eAmbient =
      DualizingAdjunction.iso U hU N K M ε I eM eN' t ht htreg bt bQ' eAmbient' := by
  exact (DualizingAdjunction.independent_target_frame U hU N K M ε I eM eN s hs hreg b bQ eAmbient eN').trans
    ((DualizingAdjunction.independent_generators U hU N K M ε I eM eN' s hs hreg b bQ eAmbient hb t ht htreg bt hbt).trans
      ((DualizingAdjunction.independent_quotient_basis U hU N K M ε I eM eN' t ht htreg bt bQ eAmbient bQ').trans
        (congrArg (fun e => DualizingAdjunction.iso U hU N K M ε I eM eN' t ht htreg bt bQ' e) he)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.AdjunctionIndependence
