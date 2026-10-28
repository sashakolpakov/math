import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicSmoothCohomologyProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.OrdinaryCech
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.CechIdentification

/-! # Cech Analytic Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison

noncomputable section

section

/-! Global smooth forms compute the native categorical Čech total,
through the existing analytic comparison and its proved augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  {ι : Type} (U : ι → X.left.Opens)

def nerve : SimplicialObject (FormalCoproduct.{0} X.left.Opens) := (FormalCoproduct.mk ι U).cech

def nativeToAnalyticIso :
    AlgebraicSmoothCechProduct.smoothTotal X (nerve X U) ≅
      Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (fun i => AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (U i)) :=
  Intrinsic.OrdinaryCech.IntrinsicOrdinary.totalIso U (AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X) ≪≫
    AlgebraicGeometry.Comparison.Betti.Analytic.CechIdentification.zariskiSmoothCechTotalIso X U

def globalToNative :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) ⟶
      AlgebraicSmoothCechProduct.smoothTotal X (nerve X U) :=
  Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X)
      (fun i => AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (U i)) ≫
    (nativeToAnalyticIso X U).inv

theorem globalToNative_comp_iso :
    globalToNative X U ≫ (nativeToAnalyticIso X U).hom =
      Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X)
        (fun i => AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (U i)) := by
  simp only [globalToNative, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable [IsSeparated X.hom] [QuasiCompact X.hom] (hU : ⨆ i, U i = ⊤)

include hU in
theorem globalToNative_quasiIso : QuasiIso (globalToNative X U) :=
  quasiIso_comp _ _ (hφ := AlgebraicGeometry.Comparison.Betti.Analytic.CechCover.analyticCechAugmentation_quasiIso X U hU)
    (hφ' := quasiIso_of_isIso _)

def globalCohomologyIso (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) n ≅
      (AlgebraicSmoothCechProduct.smoothTotal X (nerve X U)).homology n := by
  let : QuasiIso (globalToNative X U) := globalToNative_quasiIso X U hU
  exact isoOfQuasiIsoAt (globalToNative X U) n

end

/-! The native-to-analytic Čech isomorphism on actual section
summands, with its normalization in Čech degree zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Simplicial

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  {ι : Type} (U : ι → X.left.Opens)

def sectionCoordinates (p a : ℕ) :
    (AlgebraicSmoothCechProduct.smoothCochains X (nerve X U) p).obj ⦋a⦌ ≅
      ModuleCat.of ℂ (Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X)
        (fun i => AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (U i)) p a) :=
  AlgebraicGeometry.Comparison.Betti.Module.CechCoordinates.moduleCechCoordinatesIso ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p) U a ≪≫
    AlgebraicGeometry.Comparison.Betti.Cech.PushforwardCoordinates.cechPushforwardCoordinatesIso (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X) U
      (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p) a

theorem ordinary_inclusion_iso (a p n : ℕ) (hap : a + p = n) :
    AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U (AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X) a p n hap ≫
        (AlgebraicGeometry.Comparison.Betti.Analytic.CechIdentification.zariskiSmoothCechTotalIso X U).hom.f n =
      (AlgebraicGeometry.Comparison.Betti.Cech.PushforwardCoordinates.cechPushforwardCoordinatesIso (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X) U
        (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p) a).hom ≫
        Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (E := AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X)
          (fun i => AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (U i)) a p n hap := by
  let P := AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X
  let Q := Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  let F := AlgebraicGeometry.Comparison.Betti.Cech.PushforwardFunctor.presheafDirectImageComplex (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X) Q
  let V := fun i => AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (U i)
  let i₀ := AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U P a p n hap
  let i₁ := AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U F a p n hap
  let i₂ := Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (E := AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) V a p n hap
  let β := (AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalMap U (AlgebraicGeometry.Comparison.Betti.Analytic.CechIdentification.zariskiSmoothPresheafDirectImageIso X).hom).f n
  let c := AlgebraicGeometry.Comparison.Betti.Cech.PushforwardFunctor.cechPushforwardBicomplexIso (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X) U Q
  let γ := (HomologicalComplex₂.total.map c.hom (.up ℕ)).f n
  let d := (AlgebraicGeometry.Comparison.Betti.Cech.PushforwardCoordinates.cechPushforwardCoordinatesIso (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X) U
    (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p) a).hom
  have hc : ModuleCat.ofHom (AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex.cechCoefficientMap U
      ((AlgebraicGeometry.Comparison.Betti.Analytic.CechIdentification.zariskiSmoothPresheafDirectImageIso X).hom.f p) a) = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    rfl
  have hβ : i₀ ≫ β = i₁ :=
    (AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion_map U
      (AlgebraicGeometry.Comparison.Betti.Analytic.CechIdentification.zariskiSmoothPresheafDirectImageIso X).hom a p n hap).trans
      ((congrArg (fun z => z ≫ i₁) hc).trans (Category.id_comp i₁))
  have hγ : i₁ ≫ γ = d ≫ i₂ :=
    (AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex U F).ιTotal_map (AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex V Q)
      c.hom (.up ℕ) a p n hap
  change i₀ ≫ (β ≫ (γ ≫ 𝟙 _)) = d ≫ i₂
  exact (congrArg (fun z => i₀ ≫ (β ≫ z)) (Category.comp_id γ)).trans
    ((Category.assoc i₀ β γ).symm.trans ((congrArg (fun z => z ≫ γ) hβ).trans hγ))

theorem inclusion_zero_iso (p : ℕ) :
    (AlgebraicSmoothCechProduct.smoothBicomplex X (nerve X U)).ιTotal (.up ℕ) p 0 p rfl ≫
        (nativeToAnalyticIso X U).hom.f p =
      (sectionCoordinates X U p 0).hom ≫
        Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (E := AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X)
          (fun i => AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (U i)) 0 p p (Nat.zero_add p) := by
  let K := AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X
  let i₀ := (Intrinsic.OrdinaryCech.IntrinsicOrdinary.nativeBicomplex U K).ιTotal (.up ℕ) p 0 p rfl
  let i₁ := AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U K 0 p p (Nat.zero_add p)
  let i₂ := Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (E := AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X)
    (fun i => AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (U i)) 0 p p (Nat.zero_add p)
  let α := (Intrinsic.OrdinaryCech.IntrinsicOrdinary.totalIso U K).hom.f p
  let β := (AlgebraicGeometry.Comparison.Betti.Analytic.CechIdentification.zariskiSmoothCechTotalIso X U).hom.f p
  let a := (AlgebraicGeometry.Comparison.Betti.Module.CechCoordinates.moduleCechCoordinatesIso (K.X p) U 0).hom
  let b := (AlgebraicGeometry.Comparison.Betti.Cech.PushforwardCoordinates.cechPushforwardCoordinatesIso (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X) U
    (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p) 0).hom
  have h₁ : i₀ ≫ α = a ≫ i₁ := Intrinsic.OrdinaryCech.IntrinsicOrdinary.inclusion_zero_totalIso U K p
  have h₂ : i₁ ≫ β = b ≫ i₂ := ordinary_inclusion_iso X U 0 p p (Nat.zero_add p)
  change i₀ ≫ (α ≫ β) = (a ≫ b) ≫ i₂
  exact (Category.assoc i₀ α β).symm.trans
    ((congrArg (fun z => z ≫ β) h₁).trans ((Category.assoc a i₁ β).trans
      ((congrArg (fun z => a ≫ z) h₂).trans (Category.assoc a b i₂).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison
