import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeTensorHomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorScalarLinearity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyScalars

/-! # Change Homology Scalar Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeHomologyScalarCompatibility

noncomputable section

/-! The comparison between new-ring homology and the underlying tensor
homology intertwines the actual action of every new-ring scalar. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

theorem baseChangeTensorHomologyIso_smul
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (b : B)
    (x : (((Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C).homology n) :
    (ChangeTensorHomology.baseChangeTensorHomologyIso (B := B) C n).hom (b • x) =
      HomologicalComplex.homologyMap
        (Tensor.CochainBicomplex.tensorCochainMap C (ModuleCat.ofHom (Cech.TensorScalarLinearity.coefficientAlgebraMultiplication (R := R) b))) n
          ((ChangeTensorHomology.baseChangeTensorHomologyIso (B := B) C n).hom x) := by
  let BC := ((Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C
  let F := ModuleCat.restrictScalars (algebraMap R B)
  let e := (Functor.mapHomologicalComplexCompIso
    (ChangeTensorHomology.moduleBaseChangeRestrictionIso (R := R) (B := B)).symm (.up ℕ)).app C
  let s : BC ⟶ BC := b • 𝟙 BC
  let t := Tensor.CochainBicomplex.tensorCochainMap C (ModuleCat.ofHom (Cech.TensorScalarLinearity.coefficientAlgebraMultiplication (R := R) b))
  have he : (F.mapHomologicalComplex (.up ℕ)).map s ≫ e.hom = e.hom ≫ t := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change B ⊗[R] C.X q at z
    change b • z = (Cech.TensorScalarLinearity.coefficientAlgebraMultiplication (R := R) b).rTensor (C.X q) z
    induction z using TensorProduct.inductionOn with
    | tmul c v =>
        simp only [TensorProduct.smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul]
        rfl
    | add z w hz hw => simp only [smul_add, map_add, hz, hw]
  have h₁ : F.map (HomologicalComplex.homologyMap s n) ≫ ((BC.sc n).mapHomologyIso F).inv =
      ((BC.sc n).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map s) n :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} B) (.up ℕ) n).map s) F
  have h₂ := congrArg (fun k => HomologicalComplex.homologyMap k n) he
  simp only [HomologicalComplex.homologyMap_comp] at h₂
  have h : F.map (HomologicalComplex.homologyMap s n) ≫
      (ChangeTensorHomology.baseChangeTensorHomologyIso (B := B) C n).hom =
        (ChangeTensorHomology.baseChangeTensorHomologyIso (B := B) C n).hom ≫ HomologicalComplex.homologyMap t n := by
    change F.map (HomologicalComplex.homologyMap s n) ≫
        (((BC.sc n).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap e.hom n) =
      (((BC.sc n).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap e.hom n) ≫
        HomologicalComplex.homologyMap t n
    rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]
  dsimp only [s] at h
  rw [CoefficientCech.HomologyScalars.cochainHomologyMap_smul, HomologicalComplex.homologyMap_id] at h
  exact ConcreteCategory.congr_hom h x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeHomologyScalarCompatibility
