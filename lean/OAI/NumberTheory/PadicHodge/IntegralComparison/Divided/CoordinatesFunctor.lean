import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.BaseChange

/-! # Coordinates Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesFunctor

noncomputable section

/-!
# IntegralComparison: natural divided-coordinate extensions on the original crystalline site

Every crystalline morphism induces a divided-power coefficient change
on the actual free divided-coordinate rings. These maps preserve the
original geometric maps and make projection and zero section natural.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (σ : Type u)
  {U V Z : BigCrystallineSite.Object p B J δ f}

def ringMap (α : U ⟶ V) :
    DividedPowers.DPMorphism (Crystalline.DividedCoordinates.object V σ).dividedPowers (Crystalline.DividedCoordinates.object U σ).dividedPowers := by
  letI : Algebra V.ring U.ring := α.ringMap.toRingHom.toAlgebra
  exact DividedPowers.DPMorphism.mk'
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.BaseChange.FreeRelativeBaseChange.map_isDPMorphism V.ring U.ring σ
      V.ideal V.dividedPowers U.ideal U.dividedPowers α.ringMap.isDPMorphism)

theorem ringMap_coefficient (α : U ⟶ V) (a : V.ring) :
    CoordinatesFunctor.ringMap σ α (algebraMap V.ring (Crystalline.DividedCoordinates.object V σ).ring a) =
      algebraMap U.ring (Crystalline.DividedCoordinates.object U σ).ring (α.ringMap a) := by
  let : Algebra V.ring U.ring := α.ringMap.toRingHom.toAlgebra
  exact AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_coefficient V.ring U.ring σ a

theorem ringMap_generator (α : U ⟶ V) (n : ℕ) (i : σ) :
    CoordinatesFunctor.ringMap σ α (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator V.ring σ n i) =
      AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator U.ring σ n i := by
  let : Algebra V.ring U.ring := α.ringMap.toRingHom.toAlgebra
  exact AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_generator V.ring U.ring σ n i

theorem ringMap_projection (α : U ⟶ V) :
    (CoordinatesFunctor.ringMap σ α).comp (Crystalline.DividedCoordinates.projection V σ).ringMap =
      (Crystalline.DividedCoordinates.projection U σ).ringMap.comp α.ringMap := by
  ext a
  exact ringMap_coefficient σ α a

theorem quotient_projection (α : U ⟶ V) :
    (BigCrystallineSite.Object.quotientMap (Crystalline.DividedCoordinates.object U σ) (Crystalline.DividedCoordinates.object V σ) (CoordinatesFunctor.ringMap σ α)).comp
        (BigCrystallineSite.Object.quotientMap (Crystalline.DividedCoordinates.object V σ) V (Crystalline.DividedCoordinates.projection V σ).ringMap) =
      (BigCrystallineSite.Object.quotientMap (Crystalline.DividedCoordinates.object U σ) U (Crystalline.DividedCoordinates.projection U σ).ringMap).comp
        (BigCrystallineSite.Object.quotientMap U V α.ringMap) := by
  rw [← BigCrystallineSite.Object.quotientMap_comp, ← BigCrystallineSite.Object.quotientMap_comp, ringMap_projection]

theorem closed_projection (α : U ⟶ V) :
    Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap (Crystalline.DividedCoordinates.object U σ) (Crystalline.DividedCoordinates.object V σ) (CoordinatesFunctor.ringMap σ α))) ≫
        Spec.map (CommRingCat.ofHom (Crystalline.DividedCoordinates.residueInclusion V σ)) =
      Spec.map (CommRingCat.ofHom (Crystalline.DividedCoordinates.residueInclusion U σ)) ≫
        Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U V α.ringMap)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) (quotient_projection σ α)

theorem ringMap_overBase (α : U ⟶ V) :
    (CoordinatesFunctor.ringMap σ α).toRingHom.comp (Crystalline.DividedCoordinates.object V σ).base = (Crystalline.DividedCoordinates.object U σ).base := by
  apply RingHom.ext
  intro b
  change CoordinatesFunctor.ringMap σ α (algebraMap V.ring (Crystalline.DividedCoordinates.object V σ).ring (V.base b)) =
    algebraMap U.ring (Crystalline.DividedCoordinates.object U σ).ring (U.base b)
  rw [ringMap_coefficient]
  exact congrArg (algebraMap U.ring (Crystalline.DividedCoordinates.object U σ).ring) (DFunLike.congr_fun α.overBase b)

theorem ringMap_overX (α : U ⟶ V) :
    Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap (Crystalline.DividedCoordinates.object U σ) (Crystalline.DividedCoordinates.object V σ) (CoordinatesFunctor.ringMap σ α))) ≫
        (Crystalline.DividedCoordinates.object V σ).mapToX = (Crystalline.DividedCoordinates.object U σ).mapToX := by
  rw [Crystalline.DividedCoordinates.object_mapToX, Crystalline.DividedCoordinates.object_mapToX, ← Category.assoc, closed_projection, Category.assoc, α.overX]

def map (α : U ⟶ V) : Crystalline.DividedCoordinates.object U σ ⟶ Crystalline.DividedCoordinates.object V σ where
  ringMap := CoordinatesFunctor.ringMap σ α
  overBase := ringMap_overBase σ α
  overX := ringMap_overX σ α

theorem map_projection (α : U ⟶ V) : CoordinatesFunctor.map σ α ≫ Crystalline.DividedCoordinates.projection V σ = Crystalline.DividedCoordinates.projection U σ ≫ α := by
  apply BigCrystallineSite.Object.Hom.ext
  exact ringMap_projection σ α

theorem zeroSection_map (α : U ⟶ V) : Crystalline.DividedCoordinates.zeroSection U σ ≫ CoordinatesFunctor.map σ α = α ≫ Crystalline.DividedCoordinates.zeroSection V σ := by
  apply BigCrystallineSite.Object.Hom.ext
  ext a
  let : Algebra V.ring U.ring := α.ringMap.toRingHom.toAlgebra
  exact AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraBaseChange.DividedAlgebraBaseChange.augmentation_map V.ring U.ring σ a

theorem map_id (U : BigCrystallineSite.Object p B J δ f) : CoordinatesFunctor.map σ (𝟙 U) = 𝟙 (Crystalline.DividedCoordinates.object U σ) := by
  apply BigCrystallineSite.Object.Hom.ext
  apply DividedPowers.DPMorphism.ext
  apply congrArg (fun g : (Crystalline.DividedCoordinates.object U σ).ring →+* (Crystalline.DividedCoordinates.object U σ).ring => (g : _ → _))
  apply AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.BaseChange.FreeRelativeBaseChange.ringHom_ext U.ring σ
  · intro a
    exact ringMap_coefficient σ (𝟙 U) a
  · intro n i
    exact ringMap_generator σ (𝟙 U) n i

theorem map_comp (α : U ⟶ V) (β : V ⟶ Z) : CoordinatesFunctor.map σ (α ≫ β) = CoordinatesFunctor.map σ α ≫ CoordinatesFunctor.map σ β := by
  apply BigCrystallineSite.Object.Hom.ext
  apply DividedPowers.DPMorphism.ext
  apply congrArg (fun g : (Crystalline.DividedCoordinates.object Z σ).ring →+* (Crystalline.DividedCoordinates.object U σ).ring => (g : _ → _))
  apply AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.BaseChange.FreeRelativeBaseChange.ringHom_ext Z.ring σ
  · intro a
    change CoordinatesFunctor.ringMap σ (α ≫ β) (algebraMap Z.ring (Crystalline.DividedCoordinates.object Z σ).ring a) =
      CoordinatesFunctor.ringMap σ α (CoordinatesFunctor.ringMap σ β (algebraMap Z.ring (Crystalline.DividedCoordinates.object Z σ).ring a))
    rw [ringMap_coefficient, ringMap_coefficient, ringMap_coefficient]
    rfl
  · intro n i
    change CoordinatesFunctor.ringMap σ (α ≫ β) (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Z.ring σ n i) =
      CoordinatesFunctor.ringMap σ α (CoordinatesFunctor.ringMap σ β (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Z.ring σ n i))
    rw [ringMap_generator, ringMap_generator, ringMap_generator]

def functor : BigCrystallineSite.Object p B J δ f ⥤ BigCrystallineSite.Object p B J δ f where
  obj U := Crystalline.DividedCoordinates.object U σ
  map α := CoordinatesFunctor.map σ α
  map_id U := CoordinatesFunctor.map_id σ U
  map_comp α β := CoordinatesFunctor.map_comp σ α β

def projectionNatTrans : functor (p := p) (B := B) (J := J) (δ := δ) (f := f) σ ⟶ 𝟭 _ where
  app U := Crystalline.DividedCoordinates.projection U σ
  naturality _ _ α := map_projection σ α

def zeroSectionNatTrans : 𝟭 _ ⟶ functor (p := p) (B := B) (J := J) (δ := δ) (f := f) σ where
  app U := Crystalline.DividedCoordinates.zeroSection U σ
  naturality _ _ α := (zeroSection_map σ α).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesFunctor
