import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.ModuleClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology

/-! # Cochain Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.CochainClass

noncomputable section

/-! The canonical coefficient comparison on cohomology sends the actual
class of a coefficient-transformed cocycle to its original class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses

universe u v u' v'
variable {R : Type u} [CommRing R] {T : Type u'} [CommRing T]

theorem short_class (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x : Module.CochainClasses.cycles K n) :
    (K.homologyIsoSc' ((ComplexShape.up ℕ).prev n) n (n+1) rfl
      (CochainComplex.next ℕ n)).hom (Module.CochainClasses.classMap K n x) =
        ModuleClass.classMap (Module.CochainClasses.short K n) x := by
  change (K.homologyIsoSc' _ n (n+1) rfl (CochainComplex.next ℕ n)).hom
      ((K.homologyIsoSc' _ n (n+1) rfl (CochainComplex.next ℕ n)).inv _) = _
  exact ConcreteCategory.congr_hom
    (Iso.inv_hom_id (K.homologyIsoSc' _ n (n+1) rfl (CochainComplex.next ℕ n))) _

variable (F : ModuleCat.{v} R ⥤ ModuleCat.{v'} T)
  [F.Additive] [F.PreservesHomology] [PreservesFiniteLimits F]
  (η : ∀ M : ModuleCat.{v} R, M →+ F.obj M)
  (hη : ∀ {M N : ModuleCat.{v} R} (f : M ⟶ N) (x : M),
    F.map f (η M x) = η N (f x))
  (K : CochainComplex (ModuleCat.{v} R) ℕ)

local notation "L" => Functor.obj (Functor.mapHomologicalComplex F (ComplexShape.up ℕ)) K

include hη in
omit [PreservesFiniteLimits F] in
theorem homology (n : ℕ) (x : Module.CochainClasses.cycles K n) (y : Module.CochainClasses.cycles L n)
    (hy : y.val = η (K.X n) x.val) :
    (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso F K n).hom (Module.CochainClasses.classMap L n y) =
      η (K.homology n) (Module.CochainClasses.classMap K n x) := by
  let s := K.homologyIsoSc' ((ComplexShape.up ℕ).prev n) n (n+1) rfl
    (CochainComplex.next ℕ n)
  let t := (L).homologyIsoSc' ((ComplexShape.up ℕ).prev n) n (n+1) rfl
    (CochainComplex.next ℕ n)
  apply (ModuleCat.mono_iff_injective (F.map s.hom)).mp inferInstance
  have hc : F.map s.hom ((AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso F K n).hom (Module.CochainClasses.classMap L n y)) =
      ((Module.CochainClasses.short K n).mapHomologyIso F).hom (t.hom (Module.CochainClasses.classMap L n y)) :=
    ConcreteCategory.congr_hom (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.shortIso F K
      ((ComplexShape.up ℕ).prev n) n (n+1) rfl (CochainComplex.next ℕ n)) _
  have ht : t.hom (Module.CochainClasses.classMap L n y) = ModuleClass.classMap (Module.CochainClasses.short L n) y :=
    short_class L n y
  have hs : s.hom (Module.CochainClasses.classMap K n x) = ModuleClass.classMap (Module.CochainClasses.short K n) x :=
    short_class K n x
  exact hc.trans ((congrArg ((Module.CochainClasses.short K n).mapHomologyIso F).hom ht).trans
    ((ModuleClass.homology F η hη (Module.CochainClasses.short K n) x y hy).trans
      ((congrArg (η (Module.CochainClasses.short K n).homology) hs).symm.trans (hη s.hom _).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.CochainClass
