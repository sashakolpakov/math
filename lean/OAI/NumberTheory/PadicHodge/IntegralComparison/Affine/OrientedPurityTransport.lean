import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrientedPurity

/-! # Oriented Purity Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrientedPurityTransport

noncomputable section

/-! Oriented affine purity commutes with equality transport of the
same quotient ideal, preserving the original augmented resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (K : ChainComplex X.Modules ℕ) [∀ k, (K.X k).IsQuasicoherent]
  (M : X.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ k, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X k))]
  [∀ k, ((LinearResolutionPurity.internalComplex N K).X k).IsQuasicoherent]
  (I J : Ideal Γ(X, U)) (h : I = J)
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(X, U) (Γ(X, U) ⧸ I))
  {c : ℕ} (s : Fin c → Γ(X, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(X, U) s = I)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn s))
  (eN : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))

theorem iso_cast :
    OrientedPurity.iso U hU N K M ε J
      (eM ≪≫ (Ideal.quotientEquivAlgOfEq Γ(X, U) h).toLinearEquiv.toModuleIso)
      s (hs.trans h) hreg eN =
    OrientedPurity.iso U hU N K M ε I eM s hs hreg eN ≪≫
      (Ideal.quotientEquivAlgOfEq Γ(X, U) h).toLinearEquiv.toModuleIso := by
  subst J
  have he : (Ideal.quotientEquivAlgOfEq Γ(X, U) (rfl : I = I)).toLinearEquiv.toModuleIso =
      Iso.refl (ModuleCat.of Γ(X, U) (Γ(X, U) ⧸ I)) := by
    apply Iso.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Ideal.quotientEquivAlgOfEq Γ(X, U) (rfl : I = I) x = x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.quotientEquivAlgOfEq_mk Γ(X, U) rfl a
  rw [he, Iso.trans_refl, Iso.trans_refl]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrientedPurityTransport
