import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.AdjunctionEvaluation

/-! # Adjunction Frame Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.AdjunctionFrameEvaluation

noncomputable section

/-! The actual adjunction map can be evaluated in any frame of the
target line. In particular it can use the frame induced by restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

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
  {k : Type u} [CommRing k] [Algebra k Γ(X, U)]
  [Algebra.Smooth k Γ(X, U)] [Algebra.Smooth k (Γ(X, U) ⧸ I)]
  {g : ℕ} (bQ : Module.Basis (Fin g) (Γ(X, U) ⧸ I) Ω[Γ(X, U) ⧸ I⁄k])
  (eAmbient : ((Γ(X, U) ⧸ I) ⊗[Γ(X, U)] (AffineOpen.InternalHom.sections U hU).obj N) ≃ₗ[Γ(X, U) ⧸ I]
    ⋀[Γ(X, U) ⧸ I]^(c + g) ((Γ(X, U) ⧸ I) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄k]))

theorem adjunction_apply_with_frame
    (x : (ModuleExactSections.sections U).obj
      ((LinearResolutionPurity.internalComplex N K).homology c)) :
    (DualizingAdjunction.iso U hU N K M ε I eM eN s hs hreg b bQ eAmbient).hom x =
      ConormalAdjunction.equivalence I b bQ
        (eAmbient ((LineValuedKoszulPurity.lineFrame Γ(X, U) I ((AffineOpen.InternalHom.sections U hU).obj N) eN').symm
          ((OrientedPurity.iso U hU N K M ε I eM s hs hreg eN').hom x))) := by
  have h := DualizingAdjunction.independent_target_frame U hU N K M ε I eM eN
    s hs hreg b bQ eAmbient eN'
  exact (congrArg (fun e => e.hom x) h).trans
    (AdjunctionEvaluation.adjunction_apply U hU N K M ε I eM eN' s hs hreg b bQ eAmbient x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.AdjunctionFrameEvaluation
