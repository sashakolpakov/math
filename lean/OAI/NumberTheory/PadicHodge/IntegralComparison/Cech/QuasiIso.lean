import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Naturality
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechPullbackBicomplex
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Basic.Complex.Basic

/-! # Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.QuasiIso

noncomputable section

/-! Reflection of native Čech quasi-isomorphisms through coefficient
forgetting and the actual direct-image coordinate isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex₂

theorem additiveCoefficients_of_pullback
    {X Y : TopCat.{0}} (g : Y ⟶ X) {ι : Type} (U : ι → Opens X)
    {K : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ}
    {L : CochainComplex ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ}
    (α : K ⟶ ((AlgebraicGeometry.Comparison.Betti.AdditiveCechPullbackBicomplex.additivePresheafDirectImage g).mapHomologicalComplex (.up ℕ)).obj L)
    (h : QuasiIso (total.map (AlgebraicGeometry.Comparison.Betti.AdditiveCechPullbackBicomplex.additiveCechPullbackBicomplexMap g U α) (.up ℕ))) :
    QuasiIso (CechCoefficient.Naturality.Total.totalMap (FormalCoproduct.mk ι U).cech α) := by
  let e := (NatIso.mapHomologicalComplex
    (AlgebraicGeometry.Comparison.Betti.AdditiveCechPullbackBicomplex.additiveCechDirectImageFunctorIso g U) (.up ℕ)).app L
  let d := total.mapIso e (.up ℕ)
  have hd : QuasiIso d.hom := quasiIso_of_isIso d.hom
  have hc : QuasiIso
      (CechCoefficient.Naturality.Total.totalMap (FormalCoproduct.mk ι U).cech α ≫ d.hom) := by
    change QuasiIso (total.map _ (.up ℕ) ≫ total.map e.hom (.up ℕ))
    erw [← total.map_comp]
    exact h
  exact quasiIso_of_comp_right _ d.hom (hφ := hd) (hφφ' := hc)

theorem moduleCoefficients_of_forget {C : Type*} [Category* C]
    (E : SimplicialObject (FormalCoproduct.{0} C))
    {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ} (f : K ⟶ L)
    (h : QuasiIso (CechCoefficient.Naturality.Total.totalMap E
      (CechCoefficient.Naturality.Total.mappedComplexMap
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) f))) :
    QuasiIso (CechCoefficient.Naturality.Total.totalMap E f) := by
  let F := forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}
  let e := CechCoefficient.Total.totalIso F E K
  let d := CechCoefficient.Total.totalIso F E L
  let g := (F.mapHomologicalComplex (.up ℕ)).map (CechCoefficient.Naturality.Total.totalMap E f)
  have hn : g ≫ d.hom = e.hom ≫ CechCoefficient.Naturality.Total.totalMap E
      (CechCoefficient.Naturality.Total.mappedComplexMap F f) :=
    CechCoefficient.Naturality.Total.totalIso_naturality F E f
  have he : QuasiIso e.hom := quasiIso_of_isIso e.hom
  have hd : QuasiIso d.hom := quasiIso_of_isIso d.hom
  have hc : QuasiIso (g ≫ d.hom) := by
    rw [hn]
    exact quasiIso_comp _ _ (hφ := he) (hφ' := h)
  have hg : QuasiIso g := quasiIso_of_comp_right g d.hom (hφ := hd) (hφφ' := hc)
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (CechCoefficient.Naturality.Total.totalMap E f) F).mp hg

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.QuasiIso
