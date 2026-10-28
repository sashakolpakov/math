import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.CochainCup

/-! # Coefficient Cochain Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientCochainCup

noncomputable section

/-! A product-preserving map after an exact coefficient change
preserves the original categorical cohomology products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality

universe u v u' v'
variable {R : Type u} [CommRing R] {S : Type u'} [CommRing S]
  (F : ModuleCat.{v} R ⥤ ModuleCat.{v'} S)
  [F.Additive] [F.PreservesHomology] [PreservesFiniteLimits F]
  (η : ∀ M : ModuleCat.{v} R, M →+ F.obj M)
  (hη : ∀ {M N : ModuleCat.{v} R} (f : M ⟶ N) (x : M),
    F.map f (η M x) = η N (f x))
  (K : CochainComplex (ModuleCat.{v} R) ℕ)
  (L : CochainComplex (ModuleCat.{v'} S) ℕ)
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)

def map (n : ℕ) : K.homology n →+ L.homology n :=
  (HomologicalComplex.homologyMap f n).hom.toAddMonoidHom.comp
    (Mapped.CochainCup.map F η K n)

def cycles (n : ℕ) : Module.CochainClasses.cycles K n →+
    Module.CochainClasses.cycles L n :=
  (Module.CochainClassNaturality.cycleMap f n).toAddMonoidHom.comp
    (Mapped.CochainCup.cycleMap F η hη K n)

omit [PreservesFiniteLimits F] in
theorem map_class (n : ℕ) (x : Module.CochainClasses.cycles K n) :
    CoefficientCochainCup.map F η K L f n (Module.CochainClasses.classMap K n x) = Module.CochainClasses.classMap L n (cycles F η hη K L f n x) :=
  (congrArg (HomologicalComplex.homologyMap f n) (Mapped.CochainCup.map_class F η hη K n x)).trans
    (Module.CochainClassNaturality.naturality_apply f n _).symm

variable
  (μ : ∀ i j, K.X i →ₗ[R] K.X j →ₗ[R] K.X (i+j))
  (ν : ∀ i j, L.X i →ₗ[S] L.X j →ₗ[S] L.X (i+j))
  (hμ : ∀ i j (x : K.X i) (y : K.X j),
    K.d (i+j) (i+j+1) (μ i j x y) =
      Cochain.CohomologyCup.cupInto K μ (i+1) j (i+j+1) (by omega) (K.d i (i+1) x) y +
      (-1 : ℤ)^i • Cochain.CohomologyCup.cupInto K μ i (j+1) (i+j+1) (by omega) x (K.d j (j+1) y))
  (hν : ∀ i j (x : L.X i) (y : L.X j),
    L.d (i+j) (i+j+1) (ν i j x y) =
      Cochain.CohomologyCup.cupInto L ν (i+1) j (i+j+1) (by omega) (L.d i (i+1) x) y +
      (-1 : ℤ)^i • Cochain.CohomologyCup.cupInto L ν i (j+1) (i+j+1) (by omega) x (L.d j (j+1) y))
  (hprod : ∀ i j (x : K.X i) (y : K.X j),
    f.f (i+j) (η (K.X (i+j)) (μ i j x y)) =
      ν i j (f.f i (η (K.X i) x)) (f.f j (η (K.X j) y)))

include hprod in
omit [F.PreservesHomology] [PreservesFiniteLimits F] in
theorem cycles_cup (i j : ℕ) (x : Module.CochainClasses.cycles K i)
    (y : Module.CochainClasses.cycles K j) :
    cycles F η hη K L f (i+j) (Cochain.CohomologyCup.cycleCup K μ hμ i j x y) =
      Cochain.CohomologyCup.cycleCup L ν hν i j (cycles F η hη K L f i x) (cycles F η hη K L f j y) :=
  Subtype.ext (hprod i j x.val y.val)

include hη hprod in
omit [PreservesFiniteLimits F] in
theorem map_cup (i j : ℕ) (x : K.homology i) (y : K.homology j) :
    CoefficientCochainCup.map F η K L f (i+j) (Cochain.CohomologyCup.cohomologyCup K μ hμ i j x y) =
      Cochain.CohomologyCup.cohomologyCup L ν hν i j (CoefficientCochainCup.map F η K L f i x) (CoefficientCochainCup.map F η K L f j y) := by
  obtain ⟨x, rfl⟩ := Module.CochainClasses.classMap_surjective K i x
  obtain ⟨y, rfl⟩ := Module.CochainClasses.classMap_surjective K j y
  rw [Cochain.CohomologyCup.cup_class, map_class F η hη, cycles_cup F η hη K L f μ ν hμ hν hprod,
    map_class F η hη, map_class F η hη, Cochain.CohomologyCup.cup_class]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientCochainCup
