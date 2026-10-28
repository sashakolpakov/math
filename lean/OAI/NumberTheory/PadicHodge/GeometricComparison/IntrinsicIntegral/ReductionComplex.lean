import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionPresheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.PresheafScalarComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinear

/-! # Reduction Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionComplex.IntrinsicIntegralReductionComplex

noncomputable section

/-! The actual coefficient-reduction morphism of native de Rham complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionPresheaf.IntrinsicIntegralReductionPresheaf
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

def direct : (Y.left.Opensᵒᵖ ⥤ ModuleCat S) ⥤ (X.left.Opensᵒᵖ ⥤ ModuleCat R) :=
  (Functor.whiskeringLeft _ _ _).obj (Opens.map f.base).op ⋙
    (Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars (algebraMap R S))

instance direct_additive : (direct R S X Y f).Additive := by
  dsimp [direct]
  infer_instance

theorem differential (n : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X n ≫ ReductionPresheaf.IntrinsicIntegralReductionPresheaf.map R S X Y f h (n + 1) =
      ReductionPresheaf.IntrinsicIntegralReductionPresheaf.map R S X Y f h n ≫
        (direct R S X Y f).map (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf S Y n) := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  have hu := congrArg (fun k => k.app U) (Intrinsic.PresheafScalarComplex.IntrinsicPresheafScalarComplex.differential R S X Y f h n)
  have hh := ConcreteCategory.congr_hom hu ((1 : S) ⊗ₜ[R] ω)
  change Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.component R S X Y f h U.unop (n + 1)
      (((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X n).app U).hom.baseChange S (1 ⊗ₜ[R] ω)) = _ at hh
  rw [LinearMap.baseChange_tmul] at hh
  change ReductionPresheaf.IntrinsicIntegralReductionPresheaf.component R S X Y f h U.unop (n + 1) ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X n).app U ω) =
    ((direct R S X Y f).map (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf S Y n)).app U
      (ReductionPresheaf.IntrinsicIntegralReductionPresheaf.component R S X Y f h U.unop n ω)
  rw [ReductionPresheaf.IntrinsicIntegralReductionPresheaf.component_eq_one_tmul, ReductionPresheaf.IntrinsicIntegralReductionPresheaf.component_eq_one_tmul]
  exact hh

def presheafComplex : CochainComplex (X.left.Opensᵒᵖ ⥤ ModuleCat R) ℕ :=
  ((direct R S X Y f).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y)

def presheafMap : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X ⟶ presheafComplex R S X Y f where
  f n := ReductionPresheaf.IntrinsicIntegralReductionPresheaf.map R S X Y f h n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    change ReductionPresheaf.IntrinsicIntegralReductionPresheaf.map R S X Y f h n ≫
        (direct R S X Y f).map ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y).d n (n + 1)) =
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X).d n (n + 1) ≫
        ReductionPresheaf.IntrinsicIntegralReductionPresheaf.map R S X Y f h (n + 1)
    rw [show (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y).d n (n + 1) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf S Y n from CochainComplex.of_d _ _ n]
    rw [show (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X).d n (n + 1) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X n from CochainComplex.of_d _ _ n]
    exact (differential R S X Y f h n).symm

def sheafComplex : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).mapHomologicalComplex
    (.up ℕ)).obj (presheafComplex R S X Y f)

def sheafMap : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X ⟶ sheafComplex R S X Y f :=
  ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).mapHomologicalComplex
    (.up ℕ)).map (presheafMap R S X Y f h)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionComplex.IntrinsicIntegralReductionComplex
