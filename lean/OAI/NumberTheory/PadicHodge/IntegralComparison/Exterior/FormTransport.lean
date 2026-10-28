import OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Form Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.FormTransport

noncomputable section

/-! An algebra isomorphism transports exterior differential forms by
their actual pullback, with the full coordinate-ring module action.
The transport respects commuting squares of algebra maps. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {k : Type u} [CommRing k] {A B : CommAlgCat.{u} k}

def linearMap (f : A ⟶ B) (n : ℕ) :
    ModuleCat.of A (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms A n) ⟶
      (ModuleCat.restrictScalars f.hom.toRingHom).obj (ModuleCat.of B (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms B n)) :=
  ModuleCat.ofHom (X := ModuleCat.of A (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms A n))
    (Y := (ModuleCat.restrictScalars f.hom.toRingHom).obj (ModuleCat.of B (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms B n)))
    { toFun := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap f n
      map_add' := (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap f n).map_add
      map_smul' := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_smul f n }

def iso (e : A ≅ B) (n : ℕ) :
    ModuleCat.of A (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms A n) ≅
      (ModuleCat.restrictScalars e.hom.hom.toRingHom).obj (ModuleCat.of B (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms B n)) :=
  (LinearEquiv.ofBijective (linearMap e.hom n).hom
    (ConcreteCategory.bijective_of_isIso ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsFunctor n).map e.hom))).toModuleIso

theorem iso_apply (e : A ≅ B) (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms A n) :
    (iso e n).hom x = AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap e.hom n x := rfl

theorem iso_symm_apply (e : A ≅ B) (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms B n) :
    (iso e n).inv x = AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap e.inv n x := by
  apply (iso e n).toLinearEquiv.injective
  change (iso e n).hom ((iso e n).inv x) = AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap e.hom n (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap e.inv n x)
  calc
    _ = x := ConcreteCategory.congr_hom (iso e n).inv_hom_id x
    _ = _ := by rw [← AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_comp, e.inv_hom_id, AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_id]

theorem naturality {A' B' : CommAlgCat.{u} k} (e : A ≅ B) (e' : A' ≅ B')
    (f : A ⟶ A') (g : B ⟶ B') (h : e.hom ≫ g = f ≫ e'.hom)
    (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms A n) :
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap g n ((iso e n).hom x) = (iso e' n).hom (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap f n x) := by
  change AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap g n (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap e.hom n x) = AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap e'.hom n (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap f n x)
  exact (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_comp e.hom g n x).symm.trans
    ((congrArg (fun a => AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap a n x) h).trans (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_comp f e'.hom n x))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.FormTransport
