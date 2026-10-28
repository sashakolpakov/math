import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.DualizingAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantEvaluation

/-! # Adjunction Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.AdjunctionEvaluation

noncomputable section

/-! Local adjunction can be evaluated as oriented purity, the inverse
target-line frame, and the actual conormal residue. This formula keeps
the native section and cohomology maps visible for restriction. -/

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

theorem purity_evaluated
    (x : (ModuleExactSections.sections U).obj
      ((LinearResolutionPurity.internalComplex N K).homology c)) :
    DeterminantAdjunction.evaluation b
        ((LineValuedPurity.iso U hU N K M ε I eM eN s hs hreg b).hom x) =
      (LineValuedKoszulPurity.lineFrame Γ(X, U) I ((AffineOpen.InternalHom.sections U hU).obj N) eN).symm
        ((OrientedPurity.iso U hU N K M ε I eM s hs hreg eN).hom x) := by
  exact LineValuedKoszulPurity.evaluated Γ(X, U) I ((AffineOpen.InternalHom.sections U hU).obj N) eN s hs hreg
    (OrientedPurity.resolution U hU K M ε I eM) b _

variable {k : Type u} [CommRing k] [Algebra k Γ(X, U)]
  [Algebra.Smooth k Γ(X, U)] [Algebra.Smooth k (Γ(X, U) ⧸ I)]
  {g : ℕ} (bQ : Module.Basis (Fin g) (Γ(X, U) ⧸ I) Ω[Γ(X, U) ⧸ I⁄k])
  (eAmbient : ((Γ(X, U) ⧸ I) ⊗[Γ(X, U)] (AffineOpen.InternalHom.sections U hU).obj N) ≃ₗ[Γ(X, U) ⧸ I]
    ⋀[Γ(X, U) ⧸ I]^(c + g) ((Γ(X, U) ⧸ I) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄k]))

theorem adjunction_apply
    (x : (ModuleExactSections.sections U).obj
      ((LinearResolutionPurity.internalComplex N K).homology c)) :
    (DualizingAdjunction.iso U hU N K M ε I eM eN s hs hreg b bQ eAmbient).hom x =
      ConormalAdjunction.equivalence I b bQ
        (eAmbient ((LineValuedKoszulPurity.lineFrame Γ(X, U) I ((AffineOpen.InternalHom.sections U hU).obj N) eN).symm
          ((OrientedPurity.iso U hU N K M ε I eM s hs hreg eN).hom x))) := by
  exact (DeterminantEvaluation.ofResidue_arrow b eAmbient
    (ConormalAdjunction.equivalence I b bQ)
    ((LineValuedPurity.iso U hU N K M ε I eM eN s hs hreg b).hom x)).trans
    (congrArg (fun z => ConormalAdjunction.equivalence I b bQ (eAmbient z))
      (purity_evaluated U hU N K M ε I eM eN s hs hreg b x))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.AdjunctionEvaluation
