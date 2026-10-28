import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FormMaps

/-! # Form Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FormIso

noncomputable section

/-!
# IntegralComparison: algebra isomorphisms preserve the original Frobenius differential-form modules
-/

open _root_.CategoryTheory

universe u

variable {k : Type u} [Field k] [Fintype k] {A B : CommAlgCat.{u} k} (e : A ≅ B) (n : ℕ)

theorem bijective : Function.Bijective (FormMaps.map e.hom n) :=
  ConcreteCategory.bijective_of_isIso ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsFunctor n).map e.hom)

def iso : DeRhamComplex.forms k A n ≅
    (ModuleCat.restrictScalars e.hom.hom.toRingHom).obj (DeRhamComplex.forms k B n) :=
  (LinearEquiv.ofBijective (FormMaps.map e.hom n).hom (bijective e n)).toModuleIso

theorem hom : (iso e n).hom = FormMaps.map e.hom n := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FormIso
