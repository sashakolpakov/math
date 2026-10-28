import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSectionGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SectionGlobalValue
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ScalarSectionGlobalValue
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsPushforward

/-! # Basis Pullback Section Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisPullbackSectionSurjectivity

noncomputable section

/-! Pullback is additive and respects structural field scalars. Lifting a
basis therefore lifts every actual section, including its exact coefficient action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped BigOperators
universe u v
variable {X Y : Scheme.{u}}

def pullbackSectionAddHom (f : X ⟶ Y) (M : Y.Modules) :
    (Line.Bundles.structureModule Y ⟶ M) →+ (Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M) where
  toFun := Ample.LineBundles.pullbackSection f
  map_zero' := by simp only [Ample.LineBundles.pullbackSection, Functor.map_zero, comp_zero]
  map_add' s t := by simp only [Ample.LineBundles.pullbackSection, Functor.map_add, Preadditive.comp_add]

theorem pullbackSection_coefficientScalar {K : Type u} [Field K]
    (f : X ⟶ Y) (p : Y ⟶ Spec (.of K)) {M : Y.Modules}
    (c : K) (s : Line.Bundles.structureModule Y ⟶ M) :
    Ample.LineBundles.pullbackSection f (Coefficient.ScalarSections.coefficientScalarSection p c s) =
      Coefficient.ScalarSections.coefficientScalarSection (f ≫ p) c (Ample.LineBundles.pullbackSection f s) := by
  apply (Global.Sections.moduleSectionHomEquiv _).injective
  rw [Pullback.SectionGlobalValue.pullbackSection_globalValue, HilbertConstruction.Field.ScalarSectionGlobalValue.coefficientScalarSection_globalValue,
    HilbertConstruction.Field.ScalarSectionGlobalValue.coefficientScalarSection_globalValue, Pullback.SectionGlobalValue.pullbackSection_globalValue, Coefficient.GlobalSectionsPushforward.schemeCoefficientMap_comp]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app_smul
    (Coefficient.ModulePresheaf.schemeCoefficientMap p c) (Global.Sections.moduleSectionHomEquiv M s)

theorem coefficientScalarSection_postcomp {K : Type u} [Field K]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of K)) {M N : Z.Modules}
    (c : K) (s : Line.Bundles.structureModule Z ⟶ M) (e : M ⟶ N) :
    Coefficient.ScalarSections.coefficientScalarSection p c s ≫ e = Coefficient.ScalarSections.coefficientScalarSection p c (s ≫ e) := by
  exact Category.assoc _ _ _

theorem pullbackSection_surjective_of_basis_lifts {K : Type u} [Field K]
    (f : X ⟶ Y) (p : Y ⟶ Spec (.of K)) (L : Y.Modules) (M : X.Modules)
    (e : (Scheme.Modules.pullback f).obj L ≅ M) {ι : Type v} [Fintype ι]
    (b : Module.Basis ι K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (f ≫ p)).obj M))
    (s : ι → (Line.Bundles.structureModule Y ⟶ L))
    (hs : ∀ i, Ample.LineBundles.pullbackSection f (s i) ≫ e.hom = BasisSectionGeneration.sectionBasisFamily (f ≫ p) M b i) :
    Function.Surjective (fun a : Line.Bundles.structureModule Y ⟶ L => Ample.LineBundles.pullbackSection f a ≫ e.hom) := by
  intro t
  let c : ι → K := fun i => b.repr (BasisSectionGeneration.coefficientSectionAddEquiv (f ≫ p) M t) i
  refine ⟨∑ i, Coefficient.ScalarSections.coefficientScalarSection p (c i) (s i), ?_⟩
  change (pullbackSectionAddHom f L (∑ i, Coefficient.ScalarSections.coefficientScalarSection p (c i) (s i))) ≫ e.hom = t
  rw [map_sum, Preadditive.sum_comp]
  calc
    _ = ∑ i, Coefficient.ScalarSections.coefficientScalarSection (f ≫ p) (c i) (BasisSectionGeneration.sectionBasisFamily (f ≫ p) M b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show pullbackSectionAddHom f L (Coefficient.ScalarSections.coefficientScalarSection p (c i) (s i)) =
          Ample.LineBundles.pullbackSection f (Coefficient.ScalarSections.coefficientScalarSection p (c i) (s i)) from rfl,
        pullbackSection_coefficientScalar, coefficientScalarSection_postcomp, hs i]
    _ = t := (BasisSectionGeneration.section_eq_basis_linearCombination (f ≫ p) M b t).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisPullbackSectionSurjectivity
