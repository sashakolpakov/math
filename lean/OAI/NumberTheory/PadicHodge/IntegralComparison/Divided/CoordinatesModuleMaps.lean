import OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesForms

/-! # Coordinates Module Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesModuleMaps

noncomputable section

/-!
# IntegralComparison: relative divided-coordinate forms retain the original base scalars

The additive restriction maps are semilinear over each ambient ring and
linear over the original crystalline base. They therefore define an
actual module-valued presheaf with the original coefficient ring.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesForms

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (σ : Type u)
  {U V : BigCrystallineSite.Object p B J δ f}

theorem formsMap_ambient_smul (α : U ⟶ V) (n : ℕ) (a : (Crystalline.DividedCoordinates.object V σ).ring) (ω : CoordinatesForms.Forms σ V n) :
    CoordinatesForms.formsMap σ α n (a • ω) = CoordinatesFunctor.ringMap σ α a • CoordinatesForms.formsMap σ α n ω := by
  let : Algebra V.ring U.ring := α.ringMap.toRingHom.toAlgebra
  exact PD.FormsCoefficientMap.formsMap_smul V.ring U.ring
    (DividedPowerAlgebra V.ring (σ →₀ V.ring)) (DividedPowerAlgebra U.ring (σ →₀ U.ring))
    (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal V.ring σ V.ideal)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers V.ring σ V.ideal V.dividedPowers)
    (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal U.ring σ U.ideal)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers U.ring σ U.ideal U.dividedPowers)
    (AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map V.ring U.ring σ)
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.BaseChange.FreeRelativeBaseChange.map_isDPMorphism V.ring U.ring σ
      V.ideal V.dividedPowers U.ideal U.dividedPowers α.ringMap.isDPMorphism) n a ω

theorem formsMap_coefficient_smul (α : U ⟶ V) (n : ℕ) (a : V.ring) (ω : CoordinatesForms.Forms σ V n) :
    CoordinatesForms.formsMap σ α n (a • ω) = α.ringMap a • CoordinatesForms.formsMap σ α n ω := by
  rw [← algebraMap_smul (Crystalline.DividedCoordinates.object V σ).ring a ω, formsMap_ambient_smul,
    CoordinatesFunctor.ringMap_coefficient, algebraMap_smul]

def formsModule (U : BigCrystallineSite.Object p B J δ f) (n : ℕ) : ModuleCat.{u} B :=
  (ModuleCat.restrictScalars U.base).obj (ModuleCat.of U.ring (CoordinatesForms.Forms σ U n))

def map (α : U ⟶ V) (n : ℕ) : formsModule σ V n ⟶ formsModule σ U n :=
  ModuleCat.ofHom (X := formsModule σ V n) (Y := formsModule σ U n)
    { toFun := CoordinatesForms.formsMap σ α n
      map_add' := (CoordinatesForms.formsMap σ α n).map_add
      map_smul' := by
        intro b ω
        have h := formsMap_coefficient_smul σ α n (V.base b) (ω : CoordinatesForms.Forms σ V n)
        exact h.trans (congrArg (fun a : U.ring => a • CoordinatesForms.formsMap σ α n (ω : CoordinatesForms.Forms σ V n))
          (DFunLike.congr_fun α.overBase b)) }

def formsPresheaf (n : ℕ) : (BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ ModuleCat.{u} B where
  obj U := formsModule σ U.unop n
  map α := CoordinatesModuleMaps.map σ α.unop n
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact DFunLike.congr_fun (CoordinatesForms.formsMap_id σ U.unop n) ω
  map_comp α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact DFunLike.congr_fun (CoordinatesForms.formsMap_comp σ β.unop α.unop n) ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesModuleMaps
