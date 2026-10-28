import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.InternalHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.InternalHomComplex
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent

/-! # Internal Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

noncomputable section

/-! On an actual affine open, sections of the internal Hom are precisely
linear maps of the affine section modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

def chartFunctor : X.Modules ⥤ (Spec Γ(X, U)).Modules :=
  Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.inv

def sections : X.Modules ⥤ ModuleCat Γ(X, U) :=
  chartFunctor U hU ⋙ Affine.InternalHom.sections

variable (M N : X.Modules)

instance chart_quasicoherent [M.IsQuasicoherent] :
    ((chartFunctor U hU).obj M).IsQuasicoherent := by
  dsimp [chartFunctor]
  infer_instance

def chartEquiv : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U) ≃+
    ((chartFunctor U hU).obj M ⟶ (chartFunctor U hU).obj N) := by
  let F := Scheme.Modules.restrictFunctor hU.isoSpec.inv
  letI : F.IsEquivalence := inferInstanceAs
    (Scheme.Modules.restrictFunctor hU.isoSpec.symm.hom).IsEquivalence
  letI : F.Additive := Functor.additive_of_preserves_binary_products F
  exact (Open.InternalHom.sectionEquiv M N U).trans
    { toEquiv := (Functor.FullyFaithful.ofFullyFaithful F).homEquiv
      map_add' f g := F.map_add }

theorem chartEquiv_precomp {M' : X.Modules} (f : M ⟶ M')
    (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M' N, U)) :
    chartEquiv U hU M N ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap f (𝟙 N)).val.app (op U) q) =
      (chartFunctor U hU).map f ≫ chartEquiv U hU M' N q := by
  change (Scheme.Modules.restrictFunctor hU.isoSpec.inv).map
    (Open.InternalHom.sectionEquiv M N U _) = _
  rw [Open.InternalHom.sectionEquiv_precomp, CategoryTheory.Functor.map_comp]
  rfl

def equiv [M.IsQuasicoherent] : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U) ≃+
    ((sections U hU).obj M ⟶ (sections U hU).obj N) := by
  let M' := (chartFunctor U hU).obj M
  let N' := (chartFunctor U hU).obj N
  letI : M'.IsQuasicoherent := by
    dsimp [M', chartFunctor]
    infer_instance
  exact (chartEquiv U hU M N).trans
    { toEquiv := Affine.InternalHom.homEquiv M' N'
      map_add' f g := by
        change Affine.InternalHom.homEquiv M' N' (f + g) =
          Affine.InternalHom.homEquiv M' N' f + Affine.InternalHom.homEquiv M' N' g
        rw [Affine.InternalHom.homEquiv_apply, Affine.InternalHom.homEquiv_apply,
          Affine.InternalHom.homEquiv_apply]
        rfl }

theorem equiv_apply [M.IsQuasicoherent] (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U)) :
    equiv U hU M N q = Affine.InternalHom.sections.map (chartEquiv U hU M N q) := by
  let : ((chartFunctor U hU).obj M).IsQuasicoherent := chart_quasicoherent U hU M
  exact Affine.InternalHom.homEquiv_apply _ _ _

theorem precomp [M.IsQuasicoherent] {M' : X.Modules} [M'.IsQuasicoherent]
    (f : M ⟶ M') (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M' N, U)) :
    equiv U hU M N ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap f (𝟙 N)).val.app (op U) q) =
      (sections U hU).map f ≫ equiv U hU M' N q := by
  simp only [equiv_apply, chartEquiv_precomp, CategoryTheory.Functor.map_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
