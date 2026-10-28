import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.OpenNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.PresheafInclusion
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.CechIdentification
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.De

/-! # Holomorphic Presheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.HolomorphicPresheaf

noncomputable section

/-! The actual open holomorphic realizations assemble into a morphism of algebraic presheaf complexes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def holomorphicPresheafOfComplexes : X.left.Opensᵒᵖ ⥤ CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  (Opens.map (Analytification.Base.analytificationMap X)).op ⋙
    Holomorphic.Presheaf.presheafOfComplexes (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

def openHolomorphicPresheafMap : Sheaves.deRhamPresheafOfComplexes X ⟶ holomorphicPresheafOfComplexes X where
  app U := Holomorphic.openHolomorphicCochainMap X U.unop
  naturality _ _ f := Holomorphic.OpenNaturality.openHolomorphicCochainMap_restrict X (leOfHom f.unop)

def zariskiHolomorphicPresheafComplex : CochainComplex (Sheaf.CochainPullback.ComplexPresheaves X) ℕ :=
  Cech.PushforwardFunctor.presheafDirectImageComplex (Analytification.Base.analytificationMap X)
    (Holomorphic.Presheaf.presheafComplex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

def presheafHolomorphicCochainMap : Sheaves.deRhamPresheafComplex X ⟶ zariskiHolomorphicPresheafComplex X :=
  (Analytic.De.deRhamPresheafTransposeIso X).inv ≫ Complex.Transpose.transposeMap (openHolomorphicPresheafMap X)

def zariskiHolomorphicSmoothInclusion :
    zariskiHolomorphicPresheafComplex X ⟶ Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X :=
  ((Cech.PushforwardFunctor.presheafDirectImage (Analytification.Base.analytificationMap X)).mapHomologicalComplex (.up ℕ)).map
      (Holomorphic.PresheafInclusion.inclusionPresheafCochainMap (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ≫
    (Analytic.CechIdentification.zariskiSmoothPresheafDirectImageIso X).inv

theorem presheafHolomorphicCochainMap_factorization :
    presheafHolomorphicCochainMap X ≫ zariskiHolomorphicSmoothInclusion X =
      Betti.Smooth.SheafMap.presheafSmoothCochainMap X := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.HolomorphicPresheaf
