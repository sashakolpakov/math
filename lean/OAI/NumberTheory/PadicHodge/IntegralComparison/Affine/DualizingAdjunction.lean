import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LineValuedPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantAdjunction

/-! # Dualizing Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.DualizingAdjunction

noncomputable section

/-! The line-valued purity map followed by conormal adjunction lands
in the actual top exterior power of quotient differentials. The map
does not depend on equations, target frames, or quotient bases. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
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
  (eN : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))
  {c : ℕ} (s : Fin c → Γ(X, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(X, U) s = I)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn s))
  (b : Module.Basis (Fin c) (Γ(X, U) ⧸ I) I.Cotangent)
  {k : Type u} [CommRing k] [Algebra k Γ(X, U)]
  [Algebra.Smooth k Γ(X, U)] [Algebra.Smooth k (Γ(X, U) ⧸ I)]
  {g : ℕ} (bQ : Module.Basis (Fin g) (Γ(X, U) ⧸ I) Ω[Γ(X, U) ⧸ I⁄k])
  (eAmbient : ((Γ(X, U) ⧸ I) ⊗[Γ(X, U)] (AffineOpen.InternalHom.sections U hU).obj N) ≃ₗ[Γ(X, U) ⧸ I]
    ⋀[Γ(X, U) ⧸ I]^(c + g) ((Γ(X, U) ⧸ I) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄k]))

def iso :
    (ModuleExactSections.sections U).obj
      ((LinearResolutionPurity.internalComplex N K).homology c) ≅
        ModuleCat.of Γ(X, U) (⋀[Γ(X, U) ⧸ I]^g Ω[Γ(X, U) ⧸ I⁄k]) :=
  LineValuedPurity.iso U hU N K M ε I eM eN s hs hreg b ≪≫
    (LinearEquiv.restrictScalars Γ(X, U)
      (((LinearEquiv.refl (Γ(X, U) ⧸ I) (⋀[Γ(X, U) ⧸ I]^c I.Cotangent)).arrowCongr eAmbient).trans
        (DeterminantAdjunction.conormal I b bQ))).toModuleIso

attribute [local irreducible] LineValuedPurity.iso DeterminantAdjunction.conormal

theorem independent_target_frame
    (eN' : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U)) :
    iso U hU N K M ε I eM eN s hs hreg b bQ eAmbient =
      iso U hU N K M ε I eM eN' s hs hreg b bQ eAmbient := by
  exact congrArg (fun e => e ≪≫
    (LinearEquiv.restrictScalars Γ(X, U)
      (((LinearEquiv.refl (Γ(X, U) ⧸ I) (⋀[Γ(X, U) ⧸ I]^c I.Cotangent)).arrowCongr eAmbient).trans
        (DeterminantAdjunction.conormal I b bQ))).toModuleIso)
    (LineValuedPurity.independent_target_frame U hU N K M ε I eM eN s hs hreg b eN')

theorem independent_quotient_basis
    (bQ' : Module.Basis (Fin g) (Γ(X, U) ⧸ I) Ω[Γ(X, U) ⧸ I⁄k]) :
    iso U hU N K M ε I eM eN s hs hreg b bQ eAmbient =
      iso U hU N K M ε I eM eN s hs hreg b bQ' eAmbient := by
  exact congrArg (fun e => LineValuedPurity.iso U hU N K M ε I eM eN s hs hreg b ≪≫
    (LinearEquiv.restrictScalars Γ(X, U)
      (((LinearEquiv.refl (Γ(X, U) ⧸ I) (⋀[Γ(X, U) ⧸ I]^c I.Cotangent)).arrowCongr eAmbient).trans e)).toModuleIso)
    (DeterminantAdjunction.quotient_basis I b bQ bQ')

variable
  (hb : ∀ i, b i = I.toCotangent (ConormalKoszulPurity.conormalVectors Γ(X, U) I s hs i))
  (t : Fin c → Γ(X, U)) (ht : Koszul.OrientedTopCohomology.ideal Γ(X, U) t = I)
  (htreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn t))
  (bt : Module.Basis (Fin c) (Γ(X, U) ⧸ I) I.Cotangent)
  (hbt : ∀ i, bt i = I.toCotangent (ConormalKoszulPurity.conormalVectors Γ(X, U) I t ht i))

include hb hbt in
theorem independent_generators :
    iso U hU N K M ε I eM eN s hs hreg b bQ eAmbient =
      iso U hU N K M ε I eM eN t ht htreg bt bQ eAmbient := by
  exact congrArg₂ (fun e₁ e₂ => e₁ ≪≫
    (LinearEquiv.restrictScalars Γ(X, U)
      (((LinearEquiv.refl (Γ(X, U) ⧸ I) (⋀[Γ(X, U) ⧸ I]^c I.Cotangent)).arrowCongr eAmbient).trans e₂)).toModuleIso)
    (LineValuedPurity.independent_generators U hU N K M ε I eM eN s hs hreg b
      hb t ht htreg bt hbt)
    (DeterminantAdjunction.conormal_basis I b bQ bt)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.DualizingAdjunction
