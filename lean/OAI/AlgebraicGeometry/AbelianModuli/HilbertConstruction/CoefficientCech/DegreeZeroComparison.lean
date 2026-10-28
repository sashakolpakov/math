import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZeroIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor

/-! # Degree Zero Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.DegreeZeroComparison

noncomputable section

/-! The additive degree-zero coefficient Cech comparison is natural in actual module morphisms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

def coefficientCechZeroSectionsAddIso {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) :
    (Module.ProductForget.moduleForget R).obj ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M) ≅
      (Module.ProductForget.moduleForget R).obj ((Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U).homology 0) :=
  IntrinsicCech.DegreeZeroIsomorphism.cechTopSectionsHZeroIso U (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf M) hU ≪≫
    (HomologyForget.coefficientCechComplexHomologyForgetIso c M U 0).symm

theorem coefficientCechZeroSectionsAddIso_naturality
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    {M N : X.Modules} (f : M ⟶ N) {ι : Type u} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) :
    (Module.ProductForget.moduleForget R).map ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).map f) ≫
        (coefficientCechZeroSectionsAddIso c N U hU).hom =
      (coefficientCechZeroSectionsAddIso c M U hU).hom ≫
        (Module.ProductForget.moduleForget R).map (HomologicalComplex.homologyMap
          ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map f) 0) := by
  let eM := HomologyForget.coefficientCechComplexHomologyForgetIso c M U 0
  let eN := HomologyForget.coefficientCechComplexHomologyForgetIso c N U 0
  let tM := IntrinsicCech.DegreeZeroIsomorphism.cechTopSectionsHZeroIso U (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf M) hU
  let tN := IntrinsicCech.DegreeZeroIsomorphism.cechTopSectionsHZeroIso U (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf N) hU
  apply ConcreteCategory.hom_ext
  intro x
  apply (ConcreteCategory.bijective_of_isIso eN.hom).injective
  have hF := ConcreteCategory.congr_hom
    (HomologyNaturality.coefficientCechComplexHomologyForgetIso_naturality c f U 0) (eM.inv (tM.hom x))
  have hZ := ConcreteCategory.congr_hom
    (IntrinsicCech.TopDegreeZero.cechTopSectionsToHZero_naturality U (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom f)) x
  have hcancel := congrArg
    (HomologicalComplex.homologyMap ((cechComplexFunctor U).map (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom f).hom) 0)
    (eM.inv_hom_id_apply (tM.hom x))
  exact (eN.inv_hom_id_apply (tN.hom (f.app ⊤ x))).trans
    ((hF.trans hcancel).trans hZ).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.DegreeZeroComparison
