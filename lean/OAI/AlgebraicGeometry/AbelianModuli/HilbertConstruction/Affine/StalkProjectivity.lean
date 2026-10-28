import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.ModuleFreenessReflection
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Stalk Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkProjectivity

noncomputable section

/-! A finitely presented module over the functions of an affine scheme is projective if its scalar extension to every local ring is free. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u

theorem affineModule_projective_of_stalkTensor_free (S : Scheme.{u}) [IsAffine S]
    (M : Type u) [AddCommGroup M] [Module Γ(S, ⊤) M] [Module.FinitePresentation Γ(S, ⊤) M]
    (hM : ∀ x : S, letI : Algebra Γ(S, ⊤) (S.presheaf.stalk x) :=
      (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
      Module.Free (S.presheaf.stalk x) ((S.presheaf.stalk x) ⊗[Γ(S, ⊤)] M)) :
    Module.Projective Γ(S, ⊤) M := by
  apply Module.projective_of_localization_maximal
  intro I hI
  have : I.IsMaximal := hI
  let p : PrimeSpectrum Γ(S, ⊤) := ⟨I, inferInstance⟩
  let x : S := (isAffineOpen_top S).fromSpec p
  let A := S.presheaf.stalk x
  let : Algebra Γ(S, ⊤) A := (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
  have : IsLocalization I.primeCompl A :=
    (isAffineOpen_top S).isLocalization_stalk' p trivial
  have : Module.Free A (A ⊗[Γ(S, ⊤)] M) := hM x
  have : IsLocalizedModule I.primeCompl (TensorProduct.mk Γ(S, ⊤) A M 1) :=
    (isLocalizedModule_iff_isBaseChange I.primeCompl A _).mpr (TensorProduct.isBaseChange Γ(S, ⊤) M A)
  have : Module.Free (Localization I.primeCompl) (LocalizedModule I.primeCompl M) :=
    Localized.ModuleFreenessReflection.free_canonical_of_isLocalizedModule_of_free I.primeCompl A (TensorProduct.mk Γ(S, ⊤) A M 1)
  exact Module.Projective.of_free

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkProjectivity
