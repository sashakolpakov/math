import OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothForms
import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.Base
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback
import OAI.Analysis.DifferentialForms.Manifold.SheafDeRham
import Mathlib.Topology.Sheaves.Functors

/-! # Sheaf Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap

noncomputable section

/-!
# The actual algebraic-to-smooth morphism of sheaf complexes

The local realizations define a map to the analytic smooth de Rham sheaf
complex pushed forward along the actual analytic-to-Zariski point map.
The sheafification adjunction then descends the constructed presheaf map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

abbrev AnalyticComplexSheaves :=
  Sheaf (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (ModuleCat.{0} ℂ)

/-- Direct image along the already constructed analytification point map. -/
def analytificationPushforward : AnalyticComplexSheaves X ⥤ Algebraic.Sheaves.ComplexSheaves X :=
  TopCat.Sheaf.pushforward (ModuleCat.{0} ℂ) (Analytification.Base.analytificationMap X)

instance analytificationPushforwardAdditive : (analytificationPushforward X).Additive where
  map_add := by intros; rfl

theorem analytificationMap_preimage (U : X.left.Opens) :
    (Opens.map (Analytification.Base.analytificationMap X)).obj U = Open.AffineIsoEvaluation.analyticOpen X U := rfl

variable [IsIntegral X.left] [Smooth X.hom]

/-- Genuine smooth forms on the analytic manifold, viewed as a complex on the Zariski site. -/
def zariskiSmoothSheafComplex : CochainComplex (Algebraic.Sheaves.ComplexSheaves X) ℕ :=
  ((analytificationPushforward X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

def zariskiSmoothPresheafComplex : CochainComplex (Betti.Sheaf.CochainPullback.ComplexPresheaves X) ℕ :=
  ((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (zariskiSmoothSheafComplex X)

theorem zariskiSmoothPresheafComplex_d (n : ℕ) :
    (zariskiSmoothPresheafComplex X).d n (n + 1) =
      (sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).map
        ((analytificationPushforward X).map
          (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheafD (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) n)) := by
  change (sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).map
      ((analytificationPushforward X).map
        ((Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)).d n (n + 1))) = _
  exact congrArg (fun d => (sheafToPresheaf (Opens.grothendieckTopology X.left)
    (ModuleCat.{0} ℂ)).map ((analytificationPushforward X).map d))
      (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex_d (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) n)

/-- The open-section realizations assemble into a morphism of actual presheaf complexes. -/
def presheafSmoothCochainMap : Algebraic.Sheaves.deRhamPresheafComplex X ⟶ zariskiSmoothPresheafComplex X :=
  CochainComplex.ofHom (fun n =>
    { app := fun U => ModuleCat.ofHom (Open.SmoothForms.openSmoothFormMap X U.unop n)
      naturality := fun U V f => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact Open.SmoothForms.openSmoothFormMap_restrict X (leOfHom f.unop) n a }) (fun n => by
      rw [Algebraic.Sheaves.deRhamPresheafComplex_d, zariskiSmoothPresheafComplex_d]
      apply NatTrans.ext
      funext U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Open.SmoothForms.openSmoothFormMap X U.unop n a) =
        Open.SmoothForms.openSmoothFormMap X U.unop (n + 1)
          ((Algebraic.Forms.algebraicDeRhamComplex Γ(X.left, U.unop)).d n (n + 1) a)
      rw [Algebraic.Forms.algebraicDeRhamComplex_d]
      exact (Open.SmoothForms.openSmoothFormMap_d X U.unop n a).symm)

/-- The actual map of sheaf complexes, obtained from the proved local formulas. -/
def algebraicToSmoothSheafMap : Algebraic.Sheaves.algebraicDeRhamSheafComplex X ⟶ zariskiSmoothSheafComplex X :=
  ((Betti.Sheaf.CochainPullback.sheafificationComplexAdjunction X).homEquiv (Algebraic.Sheaves.deRhamPresheafComplex X)
    (zariskiSmoothSheafComplex X)).symm (presheafSmoothCochainMap X)

/-- Sheafification preserves the explicitly constructed open-section map. -/
theorem algebraicToSmoothSheafMap_normalization :
    (Betti.Sheaf.CochainPullback.sheafificationComplexAdjunction X).homEquiv (Algebraic.Sheaves.deRhamPresheafComplex X)
      (zariskiSmoothSheafComplex X) (algebraicToSmoothSheafMap X) = presheafSmoothCochainMap X :=
  (Betti.Sheaf.CochainPullback.sheafificationComplexAdjunction X).homEquiv _ _ |>.apply_symm_apply _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap
