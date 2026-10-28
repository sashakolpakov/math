import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.HolomorphicSheafMap

/-! # Sheaf Factorization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafFactorization

noncomputable section

/-! Sheafification preserves the actual algebraic-to-smooth comparison through holomorphic forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem zariskiHolomorphicSheafUnit_smooth :
    Algebraic.HolomorphicSheafMap.zariskiHolomorphicSheafUnit X ≫
        ((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
          (.up ℕ)).map (Algebraic.HolomorphicSheafMap.zariskiHolomorphicSmoothSheafMap X) =
      Algebraic.HolomorphicPresheaf.zariskiHolomorphicSmoothInclusion X := by
  let D : CochainComplex ((Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ ⥤
      CochainComplex (X.left.Opensᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ :=
    (Cech.PushforwardFunctor.presheafDirectImage (Analytification.Base.analytificationMap X)).mapHomologicalComplex (.up ℕ)
  let G := (sheafToPresheaf (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (ModuleCat.{0} ℂ)).mapHomologicalComplex (.up ℕ)
  let u := (SheafComplex.complexSheafificationAdjunction (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)).unit.app
    (Presheaf.presheafComplex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  let i := SheafComplex.inclusionSheafMap (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  have he : D.map ((SheafComplex.smoothSheafUnderlyingIso
      (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)).inv) =
      (Analytic.CechIdentification.zariskiSmoothPresheafDirectImageIso X).inv := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl
  change D.map u ≫ D.map (G.map i) =
    D.map (PresheafInclusion.inclusionPresheafCochainMap (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ≫
      (Analytic.CechIdentification.zariskiSmoothPresheafDirectImageIso X).inv
  erw [← D.map_comp]
  have hn : u ≫ G.map i =
      PresheafInclusion.inclusionPresheafCochainMap (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) ≫
        (SheafComplex.smoothSheafUnderlyingIso (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)).inv :=
    SheafComplex.inclusionSheafMap_normalization (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  erw [hn, D.map_comp, he]
  rfl

theorem algebraicToHolomorphicSheafMap_factorization :
    Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X ≫ Algebraic.HolomorphicSheafMap.zariskiHolomorphicSmoothSheafMap X =
      Betti.Smooth.SheafMap.algebraicToSmoothSheafMap X := by
  apply ((Sheaf.CochainPullback.sheafificationComplexAdjunction X).homEquiv (Algebraic.Sheaves.deRhamPresheafComplex X)
    (Betti.Smooth.SheafMap.zariskiSmoothSheafComplex X)).injective
  rw [Betti.Smooth.SheafMap.algebraicToSmoothSheafMap_normalization]
  change (Sheaf.CochainPullback.sheafificationComplexAdjunction X).unit.app (Algebraic.Sheaves.deRhamPresheafComplex X) ≫
    ((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (.up ℕ)).map (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X ≫ Algebraic.HolomorphicSheafMap.zariskiHolomorphicSmoothSheafMap X) = _
  erw [Functor.map_comp, ← Category.assoc, Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap_normalization,
    Category.assoc, zariskiHolomorphicSheafUnit_smooth,
    Algebraic.HolomorphicPresheaf.presheafHolomorphicCochainMap_factorization]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafFactorization
