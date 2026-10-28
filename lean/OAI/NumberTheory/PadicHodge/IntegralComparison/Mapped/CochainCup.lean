import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.CochainClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CupNaturality

/-! # Cochain Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.CochainCup

noncomputable section

/-! An exact coefficient change preserving actual cochain products
preserves the products on the original categorical cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CupNaturality.Cohomology

universe u v u' v'
variable {R : Type u} [CommRing R] {T : Type u'} [CommRing T]
  (F : ModuleCat.{v} R ⥤ ModuleCat.{v'} T)
  [F.Additive] [F.PreservesHomology] [PreservesFiniteLimits F]
  (η : ∀ M : ModuleCat.{v} R, M →+ F.obj M)
  (hη : ∀ {M N : ModuleCat.{v} R} (f : M ⟶ N) (x : M),
    F.map f (η M x) = η N (f x))
  (K : CochainComplex (ModuleCat.{v} R) ℕ)

local notation "L" => Functor.obj (Functor.mapHomologicalComplex F (ComplexShape.up ℕ)) K

def cycleMap (n : ℕ) : Module.CochainClasses.cycles K n →+ Module.CochainClasses.cycles L n where
  toFun x := ⟨η (K.X n) x.val, (hη (K.d n (n+1)) x.val).trans
    ((congrArg (η (K.X (n+1))) x.property).trans (map_zero _))⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

def map (n : ℕ) : K.homology n →+ (L).homology n :=
  (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso F K n).inv.hom.toAddMonoidHom.comp (η (K.homology n))

omit [PreservesFiniteLimits F] in
theorem map_class (n : ℕ) (x : Module.CochainClasses.cycles K n) :
    CochainCup.map F η K n (Module.CochainClasses.classMap K n x) = Module.CochainClasses.classMap L n (cycleMap F η hη K n x) := by
  apply (ModuleCat.mono_iff_injective (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso F K n).hom).mp inferInstance
  have h := CochainClass.homology F η hη K n x (cycleMap F η hη K n x) rfl
  exact (ConcreteCategory.congr_hom (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso F K n).inv_hom_id
    (η (K.homology n) (Module.CochainClasses.classMap K n x))).trans h.symm

variable
  (μ : ∀ i j, K.X i →ₗ[R] K.X j →ₗ[R] K.X (i+j))
  (ν : ∀ i j, ((F.mapHomologicalComplex (.up ℕ)).obj K).X i →ₗ[T] ((F.mapHomologicalComplex (.up ℕ)).obj K).X j →ₗ[T] ((F.mapHomologicalComplex (.up ℕ)).obj K).X (i+j))
  (hμ : ∀ i j (x : K.X i) (y : K.X j),
    K.d (i+j) (i+j+1) (μ i j x y) =
      Cochain.CohomologyCup.cupInto K μ (i+1) j (i+j+1) (by omega) (K.d i (i+1) x) y +
      (-1 : ℤ)^i • Cochain.CohomologyCup.cupInto K μ i (j+1) (i+j+1) (by omega) x (K.d j (j+1) y))
  (hν : ∀ i j (x : ((F.mapHomologicalComplex (.up ℕ)).obj K).X i) (y : ((F.mapHomologicalComplex (.up ℕ)).obj K).X j),
    ((F.mapHomologicalComplex (.up ℕ)).obj K).d (i+j) (i+j+1) (ν i j x y) =
      Cochain.CohomologyCup.cupInto ((F.mapHomologicalComplex (.up ℕ)).obj K) ν (i+1) j (i+j+1) (by omega) (((F.mapHomologicalComplex (.up ℕ)).obj K).d i (i+1) x) y +
      (-1 : ℤ)^i • Cochain.CohomologyCup.cupInto ((F.mapHomologicalComplex (.up ℕ)).obj K) ν i (j+1) (i+j+1) (by omega) x (((F.mapHomologicalComplex (.up ℕ)).obj K).d j (j+1) y))
  (hprod : ∀ i j (x : K.X i) (y : K.X j),
    η (K.X (i+j)) (μ i j x y) = ν i j (η (K.X i) x) (η (K.X j) y))

include hprod in
omit [F.PreservesHomology] [PreservesFiniteLimits F] in
theorem cycle_cup (i j : ℕ) (x : Module.CochainClasses.cycles K i) (y : Module.CochainClasses.cycles K j) :
    cycleMap F η hη K (i+j) (Cochain.CohomologyCup.cycleCup K μ hμ i j x y) =
      Cochain.CohomologyCup.cycleCup L ν hν i j (cycleMap F η hη K i x) (cycleMap F η hη K j y) :=
  Subtype.ext (hprod i j x.val y.val)

include hη hprod in
omit [PreservesFiniteLimits F] in
theorem map_cup (i j : ℕ) (x : K.homology i) (y : K.homology j) :
    CochainCup.map F η K (i+j) (Cochain.CohomologyCup.cohomologyCup K μ hμ i j x y) =
      Cochain.CohomologyCup.cohomologyCup L ν hν i j (CochainCup.map F η K i x) (CochainCup.map F η K j y) := by
  obtain ⟨x, rfl⟩ := Module.CochainClasses.classMap_surjective K i x
  obtain ⟨y, rfl⟩ := Module.CochainClasses.classMap_surjective K j y
  rw [Cochain.CohomologyCup.cup_class, map_class F η hη, cycle_cup F η hη K μ ν hμ hν hprod,
    map_class F η hη, map_class F η hη, Cochain.CohomologyCup.cup_class]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.CochainCup
