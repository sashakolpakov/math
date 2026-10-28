import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars

/-! # Form Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FormMaps

noncomputable section

/-!
# IntegralComparison: actual differential-form pullback respects Frobenius coordinate actions
-/

open _root_.CategoryTheory

universe u

variable {k : Type u} [Field k] [Fintype k] {A B : CommAlgCat.{u} k} (f : A ⟶ B)

theorem frobenius (a : A) : f (FiniteField.frobeniusAlgHom k A a) =
    FiniteField.frobeniusAlgHom k B (f a) := map_pow f.hom a (Fintype.card k)

def map (n : ℕ) : DeRhamComplex.forms k A n ⟶
    (ModuleCat.restrictScalars f.hom.toRingHom).obj (DeRhamComplex.forms k B n) :=
  ModuleCat.ofHom (X := DeRhamComplex.forms k A n)
    (Y := (ModuleCat.restrictScalars f.hom.toRingHom).obj (DeRhamComplex.forms k B n))
    { toFun := fun ω => AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n ω
      map_add' := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n).map_add
      map_smul' := by
        intro a ω
        change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n
          ((FiniteField.frobeniusAlgHom k A a) • (show AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k A n from ω)) =
          (FiniteField.frobeniusAlgHom k B (f a)) • AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n ω
        exact (OrdinaryFormScalars.Ordinary.formMap_smul k A B f.hom n
          (FiniteField.frobeniusAlgHom k A a) ω).trans
            (congrArg (fun b => b • AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n ω) (frobenius f a)) }

theorem differential (n : ℕ) : FormMaps.map f n ≫
    (ModuleCat.restrictScalars f.hom.toRingHom).map (DeRhamComplex.differential k B n) =
      DeRhamComplex.differential k A n ≫ FormMaps.map f (n + 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_differential f n ω).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FormMaps
