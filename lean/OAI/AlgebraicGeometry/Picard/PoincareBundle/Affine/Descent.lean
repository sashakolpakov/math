import Mathlib.Algebra.Category.ModuleCat.Descent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.LineDescent

/-! # Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Descent

noncomputable section

/-!
# Effective affine module descent for PoincareBundle

A descent datum is a coalgebra for the standard extension/restriction
of scalars comonad. Its counit and coassociativity fields are the descent
compatibility equations, not an assertion that a descended module exists.
The descended module is constructed using the proved faithfully flat
comonadicity theorem.
-/

open _root_.CategoryTheory _root_.ModuleCat
open TensorProduct

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- An S-module with the standard affine descent coaction. -/
abbrev ModuleDatum (f : R →+* S) :=
  (extendRestrictScalarsAdj f).toComonad.Coalgebra

/-- Faithfully flat module descent is an equivalence of categories. -/
def descentEquivalence (f : R →+* S) (hf : f.FaithfullyFlat) :
    ModuleCat.{u} R ≌ ModuleDatum f := by
  have : (Comonad.comparison (extendRestrictScalarsAdj f)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  exact (Comonad.comparison (extendRestrictScalarsAdj f)).asEquivalence

/-- The R-module obtained by effective descent of the supplied coaction. -/
def descendedModule (f : R →+* S) (hf : f.FaithfullyFlat) (D : ModuleDatum f) :
    ModuleCat.{u} R :=
  (descentEquivalence f hf).inverse.obj D

/-- The descent coaction, not only the underlying S-module, is recovered. -/
def descentDataIso (f : R →+* S) (hf : f.FaithfullyFlat) (D : ModuleDatum f) :
    (Comonad.comparison (extendRestrictScalarsAdj f)).obj (descendedModule f hf D) ≅ D :=
  (descentEquivalence f hf).counitIso.app D

/-- Base change of the constructed R-module recovers the original S-module. -/
def baseChangeIso (f : R →+* S) (hf : f.FaithfullyFlat) (D : ModuleDatum f) :
    (extendScalars f).obj (descendedModule f hf D) ≅ D.A :=
  (extendRestrictScalarsAdj f).toComonad.forget.mapIso (descentDataIso f hf D)

/-- Uniqueness of the descended module up to an isomorphism, with the
descent datum retained in the hypothesis. -/
theorem descendedModule_unique (f : R →+* S) (hf : f.FaithfullyFlat)
    (D : ModuleDatum f) (M : ModuleCat.{u} R)
    (e : (Comonad.comparison (extendRestrictScalarsAdj f)).obj M ≅ D) :
    Nonempty (M ≅ descendedModule f hf D) := by
  have : (Comonad.comparison (extendRestrictScalarsAdj f)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  exact ⟨(Comonad.comparison (extendRestrictScalarsAdj f)).preimageIso
    (e ≪≫ (descentDataIso f hf D).symm)⟩

/-- Effective descent of a line module over a noetherian affine base:
the module constructed from the coaction is itself invertible. -/
theorem descendedModule_invertible
    [IsNoetherianRing R] (f : R →+* S) (hf : f.FaithfullyFlat)
    (D : ModuleDatum f) [Module.Invertible S D.A] :
    Module.Invertible R (descendedModule f hf D) := by
  let : Algebra R S := f.toAlgebra
  have : Module.FaithfullyFlat R S := hf
  have : Module.Invertible S (S ⊗[R] (descendedModule f hf D)) :=
    Module.Invertible.congr (baseChangeIso f hf D).symm.toLinearEquiv
  exact LineDescent.invertible_of_faithfullyFlat_baseChange_noetherian
    R S (descendedModule f hf D)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Descent
