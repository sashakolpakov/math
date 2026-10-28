import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FormIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-! # Presheaf Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.PresheafRestriction

noncomputable section

/-!
# IntegralComparison: native Frobenius module presheaves commute with isomorphic restriction of coefficient algebras
-/

open _root_.CategoryTheory

universe u v w

variable {k : Type u} [Field k] [Fintype k] {C D : Type v} [Category.{w} C] [Category.{w} D]
  (F : C ⥤ D) (H : Dᵒᵖ ⥤ CommAlgCat.{u} k) (K : Cᵒᵖ ⥤ CommAlgCat.{u} k) (e : K ≅ F.op ⋙ H)

def ringMap : DeRhamPresheaf.rings k K ⟶ F.op ⋙ DeRhamPresheaf.rings k H :=
  Functor.whiskerRight e.hom (forget₂ (CommAlgCat.{u} k) CommRingCat ⋙ forget₂ CommRingCat RingCat)

def formsIso (n : ℕ) : DeRhamPresheaf.forms k K n ≅
    (PresheafOfModules.pushforward (ringMap F H K e)).obj (DeRhamPresheaf.forms k H n) :=
  PresheafOfModules.isoMk (fun U => FormIso.iso (e.app U) n)
    (by
      intro U V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      exact (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_comp (K.map f) (e.hom.app V) n ω).symm.trans
        ((congrArg (fun g => AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap g n ω) (e.hom.naturality f)).trans
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_comp (e.hom.app U) (H.map (F.op.map f)) n ω)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.PresheafRestriction
