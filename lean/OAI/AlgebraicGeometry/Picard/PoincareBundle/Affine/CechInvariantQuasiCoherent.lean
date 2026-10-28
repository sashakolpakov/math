import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeExact

/-! # Cech Invariant Quasi Coherent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechInvariantQuasiCoherent

noncomputable section

/-!
# The raw affine Čech invariant sheaf is quasi-coherent
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- An equalizer of maps between quasi-coherent sheaves on an affine scheme is quasi-coherent. -/
theorem equalizer_isQuasicoherent {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a b : M ⟶ N) :
    (equalizer a b).IsQuasicoherent := by
  apply TildeExact.limit_isQuasicoherent
  intro j
  cases j with
  | zero => exact inferInstanceAs M.IsQuasicoherent
  | one => exact inferInstanceAs N.IsQuasicoherent

variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (p q : S ⟶ T)
  (h : Spec.map p ≫ Spec.map f = Spec.map q ≫ Spec.map f)
  (M : (Spec S).Modules) [M.IsQuasicoherent]
  (σ : (Scheme.Modules.pullback (Spec.map p)).obj M ≅
    (Scheme.Modules.pullback (Spec.map q)).obj M)

/-- The globally defined Čech equalizer is quasi-coherent for affine coordinate maps. -/
theorem invariantSheaf_isQuasicoherent :
    (Geometric.CechInvariant.invariantSheaf (Spec.map f) (Spec.map p) (Spec.map q) h M σ).IsQuasicoherent := by
  have : ((Scheme.Modules.pushforward (Spec.map f)).obj M).IsQuasicoherent :=
    QuasiCoherent.pushforward_isQuasicoherent f M
  have : ((Scheme.Modules.pullback (Spec.map q)).obj M).IsQuasicoherent :=
    QuasiCoherent.pullback_isQuasicoherent q M
  have : ((Scheme.Modules.pushforward (Spec.map q)).obj
      ((Scheme.Modules.pullback (Spec.map q)).obj M)).IsQuasicoherent :=
    QuasiCoherent.pushforward_isQuasicoherent q _
  have : ((Scheme.Modules.pushforward (Spec.map q) ⋙ Scheme.Modules.pushforward (Spec.map f)).obj
      ((Scheme.Modules.pullback (Spec.map q)).obj M)).IsQuasicoherent :=
    QuasiCoherent.pushforward_isQuasicoherent f _
  exact equalizer_isQuasicoherent _ _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechInvariantQuasiCoherent
