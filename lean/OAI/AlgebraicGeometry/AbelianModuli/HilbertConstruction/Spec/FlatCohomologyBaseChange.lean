import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.PositiveBaseChangeLinearity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BaseChangeHomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AllDegreeComparison

/-! # Flat Cohomology Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.FlatCohomologyBaseChange

noncomputable section

/-! Flat affine base change of positive line-bundle cohomology, with the
comparison linear over the actual new affine coordinate algebra. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def specFlatLineBundleCohomologyBaseChangeIso
    {S X : Scheme.{u}} [IsAffine S] [X.IsSeparated]
    {B : Type u} [CommRing B] {P : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Spec (.of B)} {f : X ⟶ S} {g : Spec (.of B) ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
    (hflat : let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra; Module.Flat Γ(S, ⊤) B)
    (n : ℕ) :
    let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra;
    (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor Γ(S, ⊤) B).obj
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom (n + 1)).obj L.sheaf) ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (CoefficientCechComparison.specPullbackCoefficientMap (b := b)) (n + 1)).obj
        (L.pullback a).sheaf := by
  let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra
  let : Module.Flat Γ(S, ⊤) B := hflat
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  let C := Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U
  have ht (M : Type u) [AddCommGroup M] [Module Γ(S, ⊤) M] :
      QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map M (𝟙 C)) := by
    change QuasiIso (((HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor M).mapHomologicalComplex (.up ℕ)).map (𝟙 C))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  exact (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor Γ(S, ⊤) B).mapIso
      (OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso f.appTop.hom L.sheaf U hU ha (n + 1)).symm ≪≫
    HilbertConstruction.Flat.BaseChangeHomology.flatBaseChangeHomologyIso C (n + 1) ≪≫
    (PositiveBaseChangeLinearity.specModelPositiveCohomologyLinearEquiv H L U hU ha he (𝟙 C) ht n).toModuleIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.FlatCohomologyBaseChange
