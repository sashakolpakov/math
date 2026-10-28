import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-! # Stalk Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.StalkFlatness

noncomputable section

/-! A module over the global ring of an affine scheme is flat if its tensor
product with every scheme stalk is flat over that stalk. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u v

theorem affineModule_flat_of_stalk_tensor (X : Scheme.{u}) [IsAffine X]
    (V : Type v) [AddCommGroup V] [Module Γ(X, ⊤) V]
    (h : ∀ x : X,
      letI : Algebra Γ(X, ⊤) (X.presheaf.stalk x) := (X.presheaf.Γgerm x).hom.toAlgebra
      Module.Flat (X.presheaf.stalk x) ((X.presheaf.stalk x) ⊗[Γ(X, ⊤)] V)) :
    Module.Flat Γ(X, ⊤) V := by
  apply Module.flat_of_localized_maximal
  intro P hP
  let p : PrimeSpectrum Γ(X, ⊤) := ⟨P, inferInstance⟩
  let x := (isAffineOpen_top X).fromSpec p
  let A := X.presheaf.stalk x
  let : Algebra Γ(X, ⊤) A := (X.presheaf.Γgerm x).hom.toAlgebra
  have : IsLocalization.AtPrime A P := (isAffineOpen_top X).isLocalization_stalk' p (by trivial)
  have : Module.Flat Γ(X, ⊤) A := IsLocalization.flat A P.primeCompl
  have : Module.Flat A (A ⊗[Γ(X, ⊤)] V) := h x
  have : Module.Flat Γ(X, ⊤) (A ⊗[Γ(X, ⊤)] V) := Module.Flat.trans Γ(X, ⊤) A _
  exact Module.Flat.of_linearEquiv (IsLocalizedModule.linearEquiv P.primeCompl
    (LocalizedModule.mkLinearMap P.primeCompl V) (TensorProduct.mk Γ(X, ⊤) A V 1))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.StalkFlatness
