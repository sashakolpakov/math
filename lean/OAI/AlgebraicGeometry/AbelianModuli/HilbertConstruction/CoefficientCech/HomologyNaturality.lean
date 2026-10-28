import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyForget
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Homology Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyNaturality

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

/-- The comparison between forgotten base-linear Cech homology and native
additive Cech homology is natural in the coefficient module. -/
@[reassoc]
theorem coefficientCechComplexHomologyForgetIso_naturality
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (Module.ProductForget.moduleForget R).map
          (HomologicalComplex.homologyMap
            ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor ρ U).map f) n) ≫
        (HomologyForget.coefficientCechComplexHomologyForgetIso ρ N U n).hom =
      (HomologyForget.coefficientCechComplexHomologyForgetIso ρ M U n).hom ≫
        HomologicalComplex.homologyMap
          ((cechComplexFunctor U).map (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom f).hom) n := by
  let a := (((Module.ProductForget.moduleForget R).mapHomologicalComplex (.up ℕ)).map
    ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor ρ U).map f))
  let b := (ComplexForget.coefficientCechComplexForgetIso ρ N U).hom
  let c := (ComplexForget.coefficientCechComplexForgetIso ρ M U).hom
  let d := (cechComplexFunctor U).map (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom f).hom
  have hcomp : a ≫ b = c ≫ d :=
    ForgetNaturality.coefficientCechComplexForgetIso_naturality ρ f U
  have hcomplex :
      HomologicalComplex.homologyMap a n ≫
          HomologicalComplex.homologyMap b n =
        HomologicalComplex.homologyMap c n ≫
          HomologicalComplex.homologyMap d n :=
    (HomologicalComplex.homologyMap_comp a b n).symm.trans
      ((congrArg (fun g => HomologicalComplex.homologyMap g n) hcomp).trans
        (HomologicalComplex.homologyMap_comp c d n))
  let φ := (HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} R) (.up ℕ) n).map
      ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor ρ U).map f)
  let β := (HomologicalComplex.shortComplexFunctor
    AddCommGrpCat.{u} (.up ℕ) n).map
      (ComplexForget.coefficientCechComplexForgetIso ρ N U).hom
  let γ := (HomologicalComplex.shortComplexFunctor
    AddCommGrpCat.{u} (.up ℕ) n).map
      (ComplexForget.coefficientCechComplexForgetIso ρ M U).hom
  let δ := (HomologicalComplex.shortComplexFunctor
    AddCommGrpCat.{u} (.up ℕ) n).map
      ((cechComplexFunctor U).map (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom f).hom)
  let iN := ((((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor ρ U).obj N).sc n).mapHomologyIso
    (Module.ProductForget.moduleForget R)).inv
  let iM := ((((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor ρ U).obj M).sc n).mapHomologyIso
    (Module.ProductForget.moduleForget R)).inv
  dsimp only [a, b, c, d, HomologicalComplex.homologyMap] at hcomplex
  change ShortComplex.homologyMap
        ((Module.ProductForget.moduleForget R).mapShortComplex.map φ) ≫
      ShortComplex.homologyMap β =
    ShortComplex.homologyMap γ ≫
      ShortComplex.homologyMap δ at hcomplex
  rw [HomologyForget.coefficientCechComplexHomologyForgetIso_hom,
    HomologyForget.coefficientCechComplexHomologyForgetIso_hom]
  dsimp only [HomologicalComplex.homologyMap]
  change (Module.ProductForget.moduleForget R).map (ShortComplex.homologyMap φ) ≫
      (iN ≫ ShortComplex.homologyMap β) =
    iM ≫ (ShortComplex.homologyMap γ ≫
      ShortComplex.homologyMap δ)
  have hnat :
      (Module.ProductForget.moduleForget R).map (ShortComplex.homologyMap φ) ≫ iN =
        iM ≫ ShortComplex.homologyMap
          ((Module.ProductForget.moduleForget R).mapShortComplex.map φ) :=
    ShortComplex.mapHomologyIso_inv_naturality φ (Module.ProductForget.moduleForget R)
  calc
    _ = ((Module.ProductForget.moduleForget R).map (ShortComplex.homologyMap φ) ≫ iN) ≫
        ShortComplex.homologyMap β :=
      (Category.assoc _ _ _).symm
    _ = (iM ≫ ShortComplex.homologyMap
          ((Module.ProductForget.moduleForget R).mapShortComplex.map φ)) ≫
        ShortComplex.homologyMap β :=
      congrArg (fun q => q ≫ ShortComplex.homologyMap β) hnat
    _ = iM ≫
        (ShortComplex.homologyMap
            ((Module.ProductForget.moduleForget R).mapShortComplex.map φ) ≫
          ShortComplex.homologyMap β) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun q => iM ≫ q) hcomplex

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyNaturality
