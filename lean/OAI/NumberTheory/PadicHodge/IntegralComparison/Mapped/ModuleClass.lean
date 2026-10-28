import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.HomologyProjection
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # Module Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.ModuleClass

noncomputable section

/-! Concrete module cycle classes commute with the canonical homology
comparison for an exact coefficient functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'
variable {R : Type u} [CommRing R] {T : Type u'} [CommRing T]
  (F : ModuleCat.{v} R ⥤ ModuleCat.{v'} T)
  [F.Additive] [F.PreservesHomology] [PreservesFiniteLimits F]
  (η : ∀ M : ModuleCat.{v} R, M →+ F.obj M)
  (hη : ∀ {M N : ModuleCat.{v} R} (f : M ⟶ N) (x : M),
    F.map f (η M x) = η N (f x))
  (S : ShortComplex (ModuleCat.{v} R))

def classMap (x : S.g.hom.ker) : S.homology :=
  S.moduleCatHomologyIso.inv (Submodule.Quotient.mk x)

theorem classMap_eq (x : S.g.hom.ker) :
    classMap S x = S.homologyπ (S.moduleCatCyclesIso.inv x) :=
  (congrArg (fun f => f x) S.moduleCatCyclesIso_inv_π).symm

include hη in
omit [PreservesFiniteLimits F] in
theorem cycles (x : S.g.hom.ker) (y : (S.map F).g.hom.ker)
    (hy : y.val = η S.X₂ x.val) :
    (S.mapCyclesIso F).hom ((S.map F).moduleCatCyclesIso.inv y) =
      η S.cycles (S.moduleCatCyclesIso.inv x) := by
  apply (ModuleCat.mono_iff_injective (F.map S.iCycles)).mp inferInstance
  have h₁ : F.map S.iCycles ((S.mapCyclesIso F).hom ((S.map F).moduleCatCyclesIso.inv y)) =
      (S.map F).iCycles ((S.map F).moduleCatCyclesIso.inv y) :=
    congrArg (fun f => f ((S.map F).moduleCatCyclesIso.inv y))
      (S.mapCyclesIso_hom_iCycles F)
  have h₂ : (S.map F).iCycles ((S.map F).moduleCatCyclesIso.inv y) = y.val :=
    congrArg (fun f => f y) (S.map F).moduleCatCyclesIso_inv_iCycles
  have h₃ : S.iCycles (S.moduleCatCyclesIso.inv x) = x.val :=
    congrArg (fun f => f x) S.moduleCatCyclesIso_inv_iCycles
  exact h₁.trans (h₂.trans (hy.trans ((congrArg (η S.X₂) h₃).symm.trans (hη _ _).symm)))

include hη in
omit [PreservesFiniteLimits F] in
theorem homology (x : S.g.hom.ker) (y : (S.map F).g.hom.ker)
    (hy : y.val = η S.X₂ x.val) :
    (S.mapHomologyIso F).hom (classMap (S.map F) y) = η S.homology (classMap S x) := by
  rw [classMap_eq, classMap_eq]
  calc
    (S.mapHomologyIso F).hom
        ((S.map F).homologyπ ((S.map F).moduleCatCyclesIso.inv y)) =
      F.map S.homologyπ ((S.mapCyclesIso F).hom ((S.map F).moduleCatCyclesIso.inv y)) :=
      congrArg (fun f => f ((S.map F).moduleCatCyclesIso.inv y))
        (HomologyProjection.projection S F)
    _ = F.map S.homologyπ (η S.cycles (S.moduleCatCyclesIso.inv x)) :=
      congrArg (F.map S.homologyπ) (ModuleClass.cycles F η hη S x y hy)
    _ = η S.homology (S.homologyπ (S.moduleCatCyclesIso.inv x)) := hη _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.ModuleClass
