import OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsCoefficientMap

/-! # Coordinates Forms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesForms

noncomputable section

/-!
# IntegralComparison: restriction maps on relative forms of actual divided-coordinate extensions

The original crystalline morphisms induce additive maps on relative
PD forms. The coefficient ring varies with the crystalline object,
and the maps commute with the actual relative differential.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (σ : Type u)
  {U V Z : BigCrystallineSite.Object p B J δ f}

abbrev Forms (U : BigCrystallineSite.Object p B J δ f) (n : ℕ) :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form U.ring (Crystalline.DividedCoordinates.object U σ).ring (Crystalline.DividedCoordinates.object U σ).ideal (Crystalline.DividedCoordinates.object U σ).dividedPowers n

def formsMap (α : U ⟶ V) (n : ℕ) : Forms σ V n →+ Forms σ U n := by
  letI : Algebra V.ring U.ring := α.ringMap.toRingHom.toAlgebra
  exact (PD.FormsCoefficientMap.formsMap V.ring U.ring
    (DividedPowerAlgebra V.ring (σ →₀ V.ring)) (DividedPowerAlgebra U.ring (σ →₀ U.ring))
    (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal V.ring σ V.ideal)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers V.ring σ V.ideal V.dividedPowers)
    (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal U.ring σ U.ideal)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers U.ring σ U.ideal U.dividedPowers)
    (AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map V.ring U.ring σ)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.BaseChange.FreeRelativeBaseChange.map_isDPMorphism V.ring U.ring σ
      V.ideal V.dividedPowers U.ideal U.dividedPowers α.ringMap.isDPMorphism) n).toAddMonoidHom

theorem formsMap_symbol (α : U ⟶ V) (n : ℕ) (a : (Crystalline.DividedCoordinates.object V σ).ring)
    (v : Fin n → (Crystalline.DividedCoordinates.object V σ).ring) :
    formsMap σ α n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol V.ring (Crystalline.DividedCoordinates.object V σ).ring (Crystalline.DividedCoordinates.object V σ).ideal
      (Crystalline.DividedCoordinates.object V σ).dividedPowers a v) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol U.ring (Crystalline.DividedCoordinates.object U σ).ring (Crystalline.DividedCoordinates.object U σ).ideal (Crystalline.DividedCoordinates.object U σ).dividedPowers
        (CoordinatesFunctor.ringMap σ α a)
        (fun i => CoordinatesFunctor.ringMap σ α (v i)) := by
  let : Algebra V.ring U.ring := α.ringMap.toRingHom.toAlgebra
  exact PD.FormsCoefficientMap.formsMap_symbol V.ring U.ring
    (DividedPowerAlgebra V.ring (σ →₀ V.ring)) (DividedPowerAlgebra U.ring (σ →₀ U.ring))
    (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal V.ring σ V.ideal)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers V.ring σ V.ideal V.dividedPowers)
    (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal U.ring σ U.ideal)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers U.ring σ U.ideal U.dividedPowers)
    (AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map V.ring U.ring σ)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.BaseChange.FreeRelativeBaseChange.map_isDPMorphism V.ring U.ring σ
      V.ideal V.dividedPowers U.ideal U.dividedPowers α.ringMap.isDPMorphism) n a v

theorem formsMap_differential (α : U ⟶ V) (n : ℕ) (ω : Forms σ V n) :
    formsMap σ α (n + 1)
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential V.ring (Crystalline.DividedCoordinates.object V σ).ring (Crystalline.DividedCoordinates.object V σ).ideal (Crystalline.DividedCoordinates.object V σ).dividedPowers n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential U.ring (Crystalline.DividedCoordinates.object U σ).ring (Crystalline.DividedCoordinates.object U σ).ideal (Crystalline.DividedCoordinates.object U σ).dividedPowers n
        (formsMap σ α n ω) := by
  let : Algebra V.ring U.ring := α.ringMap.toRingHom.toAlgebra
  exact PD.FormsCoefficientMap.formsMap_differential V.ring U.ring
    (DividedPowerAlgebra V.ring (σ →₀ V.ring)) (DividedPowerAlgebra U.ring (σ →₀ U.ring))
    (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal V.ring σ V.ideal)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers V.ring σ V.ideal V.dividedPowers)
    (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal U.ring σ U.ideal)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers U.ring σ U.ideal U.dividedPowers)
    (AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map V.ring U.ring σ)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.BaseChange.FreeRelativeBaseChange.map_isDPMorphism V.ring U.ring σ
      V.ideal V.dividedPowers U.ideal U.dividedPowers α.ringMap.isDPMorphism) n ω

theorem ringMap_id_apply (U : BigCrystallineSite.Object p B J δ f) (a : (Crystalline.DividedCoordinates.object U σ).ring) :
    CoordinatesFunctor.ringMap σ (𝟙 U) a = a := by
  have h := congrArg (fun t : Crystalline.DividedCoordinates.object U σ ⟶ Crystalline.DividedCoordinates.object U σ => t.ringMap a)
    (CoordinatesFunctor.map_id σ U)
  exact h

theorem ringMap_comp_apply (α : U ⟶ V) (β : V ⟶ Z) (a : (Crystalline.DividedCoordinates.object Z σ).ring) :
    CoordinatesFunctor.ringMap σ (α ≫ β) a =
      CoordinatesFunctor.ringMap σ α (CoordinatesFunctor.ringMap σ β a) := by
  have h := congrArg (fun t : Crystalline.DividedCoordinates.object U σ ⟶ Crystalline.DividedCoordinates.object Z σ => t.ringMap a)
    (CoordinatesFunctor.map_comp σ α β)
  exact h

theorem formsMap_id (U : BigCrystallineSite.Object p B J δ f) (n : ℕ) :
    formsMap σ (𝟙 U) n = AddMonoidHom.id (Forms σ U n) := by
  apply PD.FormsCoefficientMap.addHom_ext U.ring (Crystalline.DividedCoordinates.object U σ).ring
    (Crystalline.DividedCoordinates.object U σ).ideal (Crystalline.DividedCoordinates.object U σ).dividedPowers
  intro a v
  rw [formsMap_symbol]
  simp only [ringMap_id_apply, AddMonoidHom.id_apply]

theorem formsMap_comp (α : U ⟶ V) (β : V ⟶ Z) (n : ℕ) :
    formsMap σ (α ≫ β) n = (formsMap σ α n).comp (formsMap σ β n) := by
  apply PD.FormsCoefficientMap.addHom_ext Z.ring (Crystalline.DividedCoordinates.object Z σ).ring
    (Crystalline.DividedCoordinates.object Z σ).ideal (Crystalline.DividedCoordinates.object Z σ).dividedPowers
  intro a v
  rw [AddMonoidHom.comp_apply, formsMap_symbol, formsMap_symbol, formsMap_symbol]
  simp only [ringMap_comp_apply]

def formsPresheaf (n : ℕ) : (BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (Forms σ U.unop n)
  map α := AddCommGrpCat.ofHom (formsMap σ α.unop n)
  map_id U := by apply AddCommGrpCat.hom_ext; exact formsMap_id σ U.unop n
  map_comp α β := by apply AddCommGrpCat.hom_ext; exact formsMap_comp σ β.unop α.unop n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesForms
