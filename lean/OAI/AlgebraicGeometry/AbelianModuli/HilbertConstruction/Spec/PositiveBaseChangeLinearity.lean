import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.ModelBaseChangeLinearity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.CoefficientCechComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity

/-! # Positive Base Change Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.PositiveBaseChangeLinearity

noncomputable section

/-! Every actual affine test algebra has a linear positive-degree comparison
with the universal finite Cech model; no special coefficient-map hypothesis is needed. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def specModelPositiveCohomologyLinearEquiv
    {S X : Scheme.{u}} [IsAffine S] [X.IsSeparated]
    {B : Type u} [CommRing B] {P : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Spec (.of B)} {f : X ⟶ S} {g : Spec (.of B) ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U)
    (ht : ∀ (M : Type u) [AddCommGroup M] [Module Γ(S, ⊤) M], QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map M φ))
    (n : ℕ) :
    let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra;
    ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor Γ(S, ⊤) B).mapHomologicalComplex (.up ℕ)).obj C).homology (n + 1)) ≃ₗ[B]
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (CoefficientCechComparison.specPullbackCoefficientMap (b := b)) (n + 1)).obj
        (L.pullback a).sheaf) := by
  let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra
  have : IsAffineHom g := isAffineHom_of_isAffine _
  have : IsAffineHom a := isAffineHom_isStableUnderBaseChange.of_isPullback H.flip inferInstance
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  have : (L.pullback a).sheaf.IsQuasicoherent := (L.pullback a).isQuasicoherent
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ) := ht (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
  have : QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫
      Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f.appTop.hom L.sheaf (CoefficientCechComparison.specPullbackCoefficientMap (b := b))
        (CoefficientCechComparison.specPullbackCoefficient_compatible H) U) (n + 1) :=
    CoefficientCechComparison.spec_affineFrame_coefficientCechModel_quasiIsoAt (H := H) (U := U) L ha he φ (n + 1)
  exact Positive.ModelBaseChangeLinearity.positiveCechModelBaseChangeLinearEquiv a f.appTop.hom L.sheaf
    (CoefficientCechComparison.specPullbackCoefficientMap (b := b)) (CoefficientCechComparison.specPullbackCoefficient_compatible H) U hU
    (Affine.CoverCechAcyclicity.IntrinsicCech.quasicoherent_affine_intersections_acyclic (L.pullback a).sheaf
      (fun i => a ⁻¹ᵁ U i) (fun i => (ha i).preimage a)) φ n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.PositiveBaseChangeLinearity
