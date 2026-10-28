import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.GeometricCechModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.ModelBaseChangeLinearity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ScalarExtensionKernel

/-! # Model Positive Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.ModelPositiveCohomology

noncomputable section

/-! The actual geometric Cech model computes positive cohomology over
the full ring of functions on an affine test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def geometricModelPositiveCohomologyLinearEquiv
    {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y] [X.IsSeparated]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U) (n : ℕ)
    [QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      CechTensorComparison.geometricCechTensorMap H L.sheaf U) (n + 1)] :
    letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra;
    (Cochain.ScalarExtensionKernel.cochainScalarExtension C Γ(Y, ⊤)).homology (n + 1) ≃ₗ[Γ(Y, ⊤)]
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom (n + 1)).obj
        (L.pullback a).sheaf) := by
  let : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  have : IsAffineHom g := isAffineHom_of_isAffine _
  have : IsAffineHom a := isAffineHom_isStableUnderBaseChange.of_isPullback H.flip inferInstance
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  have : (L.pullback a).sheaf.IsQuasicoherent := (L.pullback a).isQuasicoherent
  let v := Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
    CechTensorComparison.geometricCechTensorPushforwardMap H L.sheaf U
  let e := OrderedCech.PushforwardComplex.orderedCoefficientCechComplexPushforwardIso a f.appTop.hom
    ((Scheme.Modules.pullback a).obj L.sheaf) U
  have : QuasiIsoAt (v ≫ e.inv) (n + 1) := by
    change QuasiIsoAt ((Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      CechTensorComparison.geometricCechTensorPushforwardMap H L.sheaf U) ≫ e.inv) (n + 1)
    rw [Category.assoc]
    exact inferInstanceAs (QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      CechTensorComparison.geometricCechTensorMap H L.sheaf U) (n + 1))
  have : QuasiIsoAt v (n + 1) := quasiIsoAt_of_comp_right v e.inv (n + 1)
  have hlin : QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
        a f.appTop.hom L.sheaf b.appTop.hom
        (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) U) (n + 1) := inferInstanceAs (QuasiIsoAt v (n + 1))
  exact @Positive.ModelBaseChangeLinearity.positiveCechModelBaseChangeLinearEquiv X P Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g) _ _ _
    a f.appTop.hom L.sheaf b.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) ι _ U hU
    (Affine.CoverCechAcyclicity.IntrinsicCech.quasicoherent_affine_intersections_acyclic (L.pullback a).sheaf
      (fun i => a ⁻¹ᵁ U i) (fun i => (ha i).preimage a)) C φ n hlin

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.ModelPositiveCohomology
