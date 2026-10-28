import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BasisGluing

/-! # Basis Gluing Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BasisGluingNormalization

noncomputable section

/-! The glued isomorphism has its prescribed value on every good
affine open, not only on a chosen cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} (M N : X.Modules) (P : X.Opens → Prop)
  (φ : ∀ (U : X.Opens) (_ : IsAffineOpen U), P U → Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U))
  (hstable : ∀ (U : X.Opens) (_ : IsAffineOpen U), P U → ∀ r : Γ(X, U), P (X.basicOpen r))
  (hφ : ∀ (U : X.Opens) (hU : IsAffineOpen U) (hP : P U) (r : Γ(X, U)) (s : Γ(M, U)),
    φ (X.basicOpen r) (hU.basicOpen r) (hstable U hU hP r)
        (M.presheaf.map (homOfLE (X.basicOpen_le r)).op s) =
      N.presheaf.map (homOfLE (X.basicOpen_le r)).op (φ U hU hP s))
  (hcover : ∀ (V : X.Opens) (x : X), x ∈ V →
    ∃ (U : X.Opens), IsAffineOpen U ∧ P U ∧ x ∈ U ∧ U ≤ V)
  (hbij : ∀ (U : X.Opens) (hU : IsAffineOpen U) (hP : P U), Function.Bijective (φ U hU hP))

theorem iso_app (U : X.Opens) (hU : IsAffineOpen U) (hP : P U) (s : Γ(M, U)) :
    (BasisGluing.iso M N P φ hstable hφ hcover hbij).hom.app U s = φ U hU hP s :=
  (BasisGluing.basisMap M N P φ hstable hφ).extend_app (BasisGluing.isBasis P hcover) ⟨U, hU, hP⟩ s

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BasisGluingNormalization
