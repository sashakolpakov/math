import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Scalar Restriction Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarRestrictionSquare

noncomputable section

/-!
# IntegralComparison: commuting ring endomorphisms identify the two actual scalar restrictions
-/

open _root_.CategoryTheory

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  (f : R →+* S) (a : R →+* R) (b : S →+* S) (h : f.comp a = b.comp f)
  (M : ModuleCat.{w} S)

def iso : (ModuleCat.restrictScalars a).obj ((ModuleCat.restrictScalars f).obj M) ≅
    (ModuleCat.restrictScalars f).obj ((ModuleCat.restrictScalars b).obj M) :=
  (ModuleCat.restrictScalarsComp'App a f (f.comp a) rfl M).symm ≪≫
    ModuleCat.restrictScalarsComp'App f b (f.comp a) h M

theorem hom_apply (x : M) : (iso f a b h M).hom x = x := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarRestrictionSquare
