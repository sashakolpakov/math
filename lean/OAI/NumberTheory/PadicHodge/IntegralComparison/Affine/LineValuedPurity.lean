import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrientedPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.LineValuedKoszulPurity

/-! # Line Valued Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LineValuedPurity

noncomputable section

/-! The native cohomology-sheaf sections identify with the conormal
determinant dual valued in the actual target line. The map is independent
of the target frame and of the regular equations. -/

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

def iso :
    (ModuleExactSections.sections U).obj
      ((LinearResolutionPurity.internalComplex N K).homology c) ≅
        ModuleCat.of Γ(X, U)
          ((⋀[Γ(X, U) ⧸ I]^c I.Cotangent) →ₗ[Γ(X, U) ⧸ I]
            ((Γ(X, U) ⧸ I) ⊗[Γ(X, U)] (AffineOpen.InternalHom.sections U hU).obj N)) :=
  LinearResolutionPurity.sectionsHomologyIso U hU N K c ≪≫
    HomologicalComplex.homologyMapIso
      (LinearResolutionPurity.sectionComplexIso U hU N K) c ≪≫
        LineValuedKoszulPurity.iso Γ(X, U) I ((AffineOpen.InternalHom.sections U hU).obj N) eN s hs hreg
          (OrientedPurity.resolution U hU K M ε I eM) b

theorem independent_target_frame
    (eN' : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U)) :
    iso U hU N K M ε I eM eN s hs hreg b = iso U hU N K M ε I eM eN' s hs hreg b := by
  unfold iso
  rw [LineValuedKoszulPurity.independent_target_frame Γ(X, U) I ((AffineOpen.InternalHom.sections U hU).obj N)
    eN s hs hreg (OrientedPurity.resolution U hU K M ε I eM) b eN']

variable
  (hb : ∀ i, b i = I.toCotangent (ConormalKoszulPurity.conormalVectors Γ(X, U) I s hs i))
  (t : Fin c → Γ(X, U)) (ht : Koszul.OrientedTopCohomology.ideal Γ(X, U) t = I)
  (htreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn t))
  (bt : Module.Basis (Fin c) (Γ(X, U) ⧸ I) I.Cotangent)
  (hbt : ∀ i, bt i = I.toCotangent (ConormalKoszulPurity.conormalVectors Γ(X, U) I t ht i))

include hb hbt in
theorem independent_generators :
    iso U hU N K M ε I eM eN s hs hreg b = iso U hU N K M ε I eM eN t ht htreg bt := by
  unfold iso
  rw [LineValuedKoszulPurity.independent_generators Γ(X, U) I ((AffineOpen.InternalHom.sections U hU).obj N)
    eN s hs hreg (OrientedPurity.resolution U hU K M ε I eM) b hb t ht htreg bt hbt]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LineValuedPurity
