import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Algebra Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPresheaf

noncomputable section

/-! The structure sheaf as algebras over a chosen ring of coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

def coefficientSectionMap (f : R →+* Γ(X, ⊤)) (U : X.Opens) : R →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp f

theorem coefficientSectionMap_restrict (f : R →+* Γ(X, ⊤))
    {U V : X.Opens} (h : V ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.comp (coefficientSectionMap f U) =
      coefficientSectionMap f V := by
  unfold coefficientSectionMap
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← X.presheaf.map_comp]
  rfl

def coefficientAlgebraSections (f : R →+* Γ(X, ⊤)) (U : X.Opens) : CommAlgCat.{u} R :=
  letI := (coefficientSectionMap f U).toAlgebra
  .of R Γ(X, U)

def coefficientAlgebraRestriction (f : R →+* Γ(X, ⊤))
    {U V : X.Opens} (h : V ≤ U) :
    coefficientAlgebraSections f U ⟶ coefficientAlgebraSections f V := by
  letI := (coefficientSectionMap f U).toAlgebra
  letI := (coefficientSectionMap f V).toAlgebra
  exact CommAlgCat.ofHom {
    __ := (X.presheaf.map (homOfLE h).op).hom
    commutes' := fun r => DFunLike.congr_fun (coefficientSectionMap_restrict f h) r }

def coefficientAlgebraPresheaf (f : R →+* Γ(X, ⊤)) :
    TopCat.Presheaf (CommAlgCat.{u} R) X where
  obj U := coefficientAlgebraSections f U.unop
  map h := coefficientAlgebraRestriction f h.unop.le
  map_id U := by ext r; exact congrArg (fun k => k r) (X.presheaf.map_id U)
  map_comp h k := by ext r; exact congrArg (fun a => a r) (X.presheaf.map_comp h k)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPresheaf
