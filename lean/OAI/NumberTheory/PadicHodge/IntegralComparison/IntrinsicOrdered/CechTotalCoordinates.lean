import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentrationNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Total

/-! # Cech Total Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechTotalCoordinates.Intrinsic

noncomputable section

/-! The literal generic ordered Čech total is naturally isomorphic to
its original base-module total, with unchanged intersection components. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

def sourceFunctor : CochainComplex X.Modules ℕ ⥤ CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ :=
  (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).mapHomologicalComplex (.up ℕ) ⋙
    (OrderedCech.Functor.Projection.functor U).mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex₂.totalFunctor (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) (.up ℕ) (.up ℕ)

def iso (K : CochainComplex X.Modules ℕ) : (sourceFunctor π U).obj K ≅
    (Cech.ConcentrationNaturality.totalFunctor π U).obj K :=
  HomologicalComplex₂.total.mapIso
    ((NatIso.mapHomologicalComplex (CechCoordinates.Intrinsic.functorIso π U)
      (.up ℕ)).app K) (.up ℕ)

theorem naturality {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) :
    (sourceFunctor π U).map a ≫ (iso π U L).hom =
      (iso π U K).hom ≫ (Cech.ConcentrationNaturality.totalFunctor π U).map a := by
  let T := HomologicalComplex₂.totalFunctor (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map
      ((NatIso.mapHomologicalComplex (CechCoordinates.Intrinsic.functorIso π U)
        (.up ℕ)).hom.naturality a)).trans (T.map_comp _ _))

theorem homology_naturality {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) (q : ℕ) :
    homologyMap ((sourceFunctor π U).map a) q ≫ (homologyMapIso (iso π U L) q).hom =
      (homologyMapIso (iso π U K) q).hom ≫
        homologyMap ((Cech.ConcentrationNaturality.totalFunctor π U).map a) q := by
  exact (homologyMap_comp _ _ q).symm.trans
    ((congrArg (fun f => homologyMap f q) (Intrinsic.naturality π U a)).trans
      (homologyMap_comp _ _ q))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechTotalCoordinates.Intrinsic
