import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPresheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarBaseChange

/-! # Algebra Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPullback

noncomputable section

/-! Pullback of functions and restriction of global coefficients as algebra maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X P : Scheme.{u}} {R : Type u} [CommRing R]

theorem coefficientSectionMap_pullback (a : P ⟶ X) (f : R →+* Γ(X, ⊤)) (U : X.Opens) :
    (a.app U).hom.comp (AlgebraPresheaf.coefficientSectionMap f U) =
      AlgebraPresheaf.coefficientSectionMap (a.appTop.hom.comp f) (a ⁻¹ᵁ U) := by
  ext r
  exact (Global.ScalarBaseChange.globalFunction_pullback_restrict a (f r) U).symm

def coefficientAlgebraPullbackApp (a : P ⟶ X) (f : R →+* Γ(X, ⊤)) (U : X.Opens) :
    AlgebraPresheaf.coefficientAlgebraSections f U ⟶
      AlgebraPresheaf.coefficientAlgebraSections (a.appTop.hom.comp f) (a ⁻¹ᵁ U) := by
  letI := (AlgebraPresheaf.coefficientSectionMap f U).toAlgebra
  letI := (AlgebraPresheaf.coefficientSectionMap (a.appTop.hom.comp f) (a ⁻¹ᵁ U)).toAlgebra
  exact CommAlgCat.ofHom {
    __ := (a.app U).hom
    commutes' := fun r => DFunLike.congr_fun (coefficientSectionMap_pullback a f U) r }

def coefficientAlgebraPullback (a : P ⟶ X) (f : R →+* Γ(X, ⊤)) :
    AlgebraPresheaf.coefficientAlgebraPresheaf f ⟶
      (TopologicalSpace.Opens.map a.base).op ⋙
        AlgebraPresheaf.coefficientAlgebraPresheaf (a.appTop.hom.comp f) where
  app U := coefficientAlgebraPullbackApp a f U.unop
  naturality U V h := by
    ext r
    exact congrArg (fun k => k r) (a.naturality h)

def coefficientAlgebraGlobalRestriction (f : R →+* Γ(P, ⊤))
    (B : CommAlgCat.{u} R) (q : B →+* Γ(P, ⊤))
    (hq : q.comp (algebraMap R B) = f) (U : P.Opens) :
    B ⟶ AlgebraPresheaf.coefficientAlgebraSections f U := by
  letI := (AlgebraPresheaf.coefficientSectionMap f U).toAlgebra
  exact CommAlgCat.ofHom {
    __ := (P.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp q
    commutes' := fun r => congrArg
      (fun s => P.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s)
      (DFunLike.congr_fun hq r) }

theorem coefficientAlgebraGlobalRestriction_naturality (f : R →+* Γ(P, ⊤))
    (B : CommAlgCat.{u} R) (q : B →+* Γ(P, ⊤))
    (hq : q.comp (algebraMap R B) = f) {U V : P.Opens} (h : V ≤ U) :
    coefficientAlgebraGlobalRestriction f B q hq U ≫ AlgebraPresheaf.coefficientAlgebraRestriction f h =
      coefficientAlgebraGlobalRestriction f B q hq V := by
  ext r
  exact congrArg (fun k => k (q r)) (P.presheaf.map_comp
    (homOfLE (show U ≤ ⊤ from le_top)).op (homOfLE h).op).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPullback
