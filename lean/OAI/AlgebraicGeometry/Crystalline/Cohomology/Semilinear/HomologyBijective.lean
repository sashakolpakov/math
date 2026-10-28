import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.QuasiIso

/-! # Homology Bijective -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.HomologyBijective.SemilinearHomologyBijective

noncomputable section

/-!
# Quasi-isomorphisms induce bijections on the actual semilinear cohomology map

The explicit cycle-quotient map agrees with left homology data after
scalar restriction. This identifies the semilinear cohomology operator
without replacing it by a separately chosen isomorphism.
-/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction

universe u

variable {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S}
  {C : CochainComplex (ModuleCat.{u} R) ℕ} {D : CochainComplex (ModuleCat.{u} S) ℕ}
  (f : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map φ C D)

def shortMap (n : ℕ) : C.sc n ⟶ (D.sc n).map (ModuleCat.restrictScalars φ) :=
  (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap f)

def cycleLinear (n : ℕ) : (C.sc n).moduleCatLeftHomologyData.K ⟶
    (ModuleCat.restrictScalars φ).obj (D.sc n).moduleCatLeftHomologyData.K :=
  ModuleCat.ofHom (X := (C.sc n).moduleCatLeftHomologyData.K)
    (Y := (ModuleCat.restrictScalars φ).obj (D.sc n).moduleCatLeftHomologyData.K) {
    toFun := NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.cycleMap f n
    map_add' := map_add (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.cycleMap f n)
    map_smul' := (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.cycleMap f n).map_smulₛₗ }

def quotientLinear (n : ℕ) : (C.sc n).moduleCatLeftHomologyData.H ⟶
    (ModuleCat.restrictScalars φ).obj (D.sc n).moduleCatLeftHomologyData.H :=
  ModuleCat.ofHom (X := (C.sc n).moduleCatLeftHomologyData.H)
    (Y := (ModuleCat.restrictScalars φ).obj (D.sc n).moduleCatLeftHomologyData.H) {
    toFun := NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.quotientMap f n
    map_add' := map_add (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.quotientMap f n)
    map_smul' := (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.quotientMap f n).map_smulₛₗ }

def leftData (n : ℕ) : ShortComplex.LeftHomologyMapData (shortMap f n)
    (C.sc n).moduleCatLeftHomologyData
    ((D.sc n).moduleCatLeftHomologyData.map (ModuleCat.restrictScalars φ)) where
  φK := cycleLinear f n
  φH := quotientLinear f n
  commi := by
    apply ModuleCat.hom_ext
    rfl
  commf' := by
    rw [ShortComplex.LeftHomologyData.map_f']
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact f.comm ((ComplexShape.up ℕ).prev n) n x
  commπ := by
    apply ModuleCat.hom_ext
    rfl

variable [QuasiIso (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap f)]

theorem quotient_bijective (n : ℕ) : Function.Bijective (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.quotientMap f n) := by
  have h : ShortComplex.QuasiIso (shortMap f n) := (quasiIsoAt_iff (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap f) n).mp inferInstance
  have hi : IsIso (quotientLinear f n) := (leftData f n).quasiIso_iff.mp h
  exact (ConcreteCategory.isIso_iff_bijective (quotientLinear f n)).mp hi

theorem homology_bijective (n : ℕ) : Function.Bijective (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap f n) := by
  have hi : Function.Bijective (C.sc n).moduleCatHomologyIso.hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have ho : Function.Bijective (D.sc n).moduleCatHomologyIso.inv :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  exact ho.comp ((quotient_bijective f n).comp hi)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.HomologyBijective.SemilinearHomologyBijective
