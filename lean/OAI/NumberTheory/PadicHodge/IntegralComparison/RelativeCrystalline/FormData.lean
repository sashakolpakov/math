import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsCoefficientMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

/-! # Form Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

noncomputable section

/-!
# IntegralComparison: relative forms for natural morphisms of actual crystalline objects

A natural transformation between two diagrams of original crystalline
objects supplies the relative coefficient algebras. Its naturality
gives the commuting square required for simultaneous change of both
ambient and coefficient rings in the actual divided-power forms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)

abbrev relativeAlgebra (U : C) : Algebra (Q.obj U).ring (H.obj U).ring :=
  (π.app U).ringMap.toRingHom.toAlgebra

abbrev Forms (U : C) (n : ℕ) : Type u :=
  letI : Algebra (Q.obj U).ring (H.obj U).ring := relativeAlgebra H Q π U
  AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form (Q.obj U).ring (H.obj U).ring (H.obj U).ideal (H.obj U).dividedPowers n

def symbol (U : C) (n : ℕ) (a : (H.obj U).ring) (t : Fin n → (H.obj U).ring) : Forms H Q π U n := by
  letI : Algebra (Q.obj U).ring (H.obj U).ring := relativeAlgebra H Q π U
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol (Q.obj U).ring (H.obj U).ring (H.obj U).ideal (H.obj U).dividedPowers a t

theorem ring_square {U V : C} (α : U ⟶ V) :
    (H.map α).ringMap.toRingHom.comp (π.app V).ringMap.toRingHom =
      (π.app U).ringMap.toRingHom.comp (Q.map α).ringMap.toRingHom :=
  congrArg (fun g : H.obj U ⟶ Q.obj V => g.ringMap.toRingHom) (π.naturality α)

abbrev coefficientAlgebra {U V : C} (α : U ⟶ V) : Algebra (Q.obj V).ring (Q.obj U).ring :=
  (Q.map α).ringMap.toRingHom.toAlgebra

abbrev compositeAlgebra {U V : C} (α : U ⟶ V) : Algebra (Q.obj V).ring (H.obj U).ring :=
  ((π.app U).ringMap.toRingHom.comp (Q.map α).ringMap.toRingHom).toAlgebra

def mapAlgHom {U V : C} (α : U ⟶ V) :
    letI : Algebra (Q.obj V).ring (H.obj V).ring := relativeAlgebra H Q π V
    letI : Algebra (Q.obj V).ring (H.obj U).ring := compositeAlgebra H Q π α
    (H.obj V).ring →ₐ[(Q.obj V).ring] (H.obj U).ring := by
  letI : Algebra (Q.obj V).ring (H.obj V).ring := relativeAlgebra H Q π V
  letI : Algebra (Q.obj V).ring (H.obj U).ring := compositeAlgebra H Q π α
  exact { (H.map α).ringMap.toRingHom with commutes' a := DFunLike.congr_fun (ring_square H Q π α) a }

def formsMap {U V : C} (α : U ⟶ V) (n : ℕ) : Forms H Q π V n →+ Forms H Q π U n := by
  letI : Algebra (Q.obj V).ring (Q.obj U).ring := coefficientAlgebra Q α
  letI : Algebra (Q.obj U).ring (H.obj U).ring := relativeAlgebra H Q π U
  letI : Algebra (Q.obj V).ring (H.obj V).ring := relativeAlgebra H Q π V
  letI : Algebra (Q.obj V).ring (H.obj U).ring := compositeAlgebra H Q π α
  letI : IsScalarTower (Q.obj V).ring (Q.obj U).ring (H.obj U).ring :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (PD.FormsCoefficientMap.formsMap (Q.obj V).ring (Q.obj U).ring
    (H.obj V).ring (H.obj U).ring (H.obj V).ideal (H.obj V).dividedPowers
    (H.obj U).ideal (H.obj U).dividedPowers (mapAlgHom H Q π α) (H.map α).ringMap.isDPMorphism n).toAddMonoidHom

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData
