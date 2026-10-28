import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.Adapter
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Transpose

/-! # Sheaf Forms Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SheafFormsAdapter.FormsAdapter

noncomputable section

/-! Comparison on the actual section presheaves and their sheaf complexes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)

def formPresheafIso (n : ℕ) : AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.formPresheaf X n ≅
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf ℂ X n :=
  NatIso.ofComponents (fun U => (Forms.Adapter.FormsAdapter.formsEquiv Γ(X.left, U.unop) n).toModuleIso) (by
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact Forms.Adapter.FormsAdapter.to62_pullback Γ(X.left, U.unop) (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.sectionRestriction X f) n ω)

theorem differential66_app (n : ℕ) (U : X.left.Opensᵒᵖ) :
    (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.presheafDifferential X n).app U =
      ModuleCat.ofHom (@AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.differential Γ(X.left, U.unop) _
        (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℂ X U.unop) n) :=
  AlgebraicGeometry.Comparison.Betti.Algebraic.Forms.algebraicDeRhamComplex_d Γ(X.left, U.unop) n

def presheafComplexIso : AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafComplex X ≅
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex ℂ X :=
  HomologicalComplex.Hom.isoOfComponents (formPresheafIso X) (by
    intro i j hij
    obtain rfl := (show i + 1 = j from hij)
    rw [AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafComplex_d]
    change (formPresheafIso X i).hom ≫
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex ℂ X).d i (i + 1) = _
    rw [show (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex ℂ X).d i (i + 1) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf ℂ X i from CochainComplex.of_d _ _ i]
    apply NatTrans.ext
    funext U
    change (formPresheafIso X i).hom.app U ≫ _ =
      (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.presheafDifferential X i).app U ≫ (formPresheafIso X (i + 1)).hom.app U
    rw [differential66_app]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact (@Forms.Adapter.FormsAdapter.to62_differential Γ(X.left, U.unop) _
      (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℂ X U.unop) i ω).symm)

def sheafComplexIso : AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X ≅
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex ℂ X :=
  ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (ComplexShape.up ℕ)).mapIso (presheafComplexIso X)

def transposeIso :
    AlgebraicGeometry.Comparison.Betti.Complex.Transpose.transpose (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X) ≅
      AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafComplex X :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    obtain rfl := (show i + 1 = j from hij)
    rw [AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafComplex_d]
    simp only [Iso.refl_hom]
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

theorem embedding_eq : ComplexShape.embeddingUpIntGE 0 = ComplexShape.embeddingUpNat := by
  unfold ComplexShape.embeddingUpIntGE ComplexShape.embeddingUpNat
  congr 1
  funext n
  exact zero_add _

def changeEmbeddingIso {C : Type*} [Category* C] [Limits.HasZeroMorphisms C] [Limits.HasZeroObject C]
    (K : CochainComplex C ℕ)
    {e e' : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ)} (h : e = e') :
    K.extend e ≅ K.extend e' := eqToIso (congrArg (K.extend ·) h)

def sectionSheafExtensionIso (e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ)) :
    ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (AlgebraicGeometry.Comparison.Betti.Complex.Transpose.transpose
        (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X ⋙ e.extendFunctor (ModuleCat.{0} ℂ))) ≅
      (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X).extend e :=
  ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso
      (AlgebraicGeometry.Comparison.Betti.Complex.Transpose.transposeExtendIso (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X) e) ≪≫
    AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso
      (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)) e
      (AlgebraicGeometry.Comparison.Betti.Complex.Transpose.transpose (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X)) ≪≫
    (e.extendFunctor (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X)).mapIso
      (((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ)).mapIso (transposeIso X))

def sheafIntExtensionIso : AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X ≅
    (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X).extend ComplexShape.embeddingUpNat :=
  sectionSheafExtensionIso X (ComplexShape.embeddingUpIntGE 0) ≪≫
    changeEmbeddingIso (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X) embedding_eq

def sheafComplexIntIso : AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X ≅
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt ℂ X :=
  sheafIntExtensionIso X ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X)).mapIso
      (sheafComplexIso X)

/-- The comparison written on the defining derived-category morphism spaces. -/
def rawCohomologyEquiv (n : ℕ) :
    (((DerivedCategory.singleFunctor (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X) 0).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf ℂ X)) ⟶
      (DerivedCategory.Q.obj (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X))⟦(n : ℤ)⟧) ≃ₗ[ℂ]
    (((DerivedCategory.singleFunctor (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X) 0).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf ℂ X)) ⟶
      (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt ℂ X))⟦(n : ℤ)⟧) :=
  Linear.homCongr ℂ (Iso.refl _)
    ((shiftFunctor (DerivedCategory (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X)) (n : ℤ)).mapIso
      (DerivedCategory.Q.mapIso (sheafComplexIntIso X)))

/-- The resulting equivalence on the independently defined hypercohomology groups. -/
def cohomologyEquiv (n : ℕ) : AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRham X n ≃ₗ[ℂ]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ X n := rawCohomologyEquiv X n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SheafFormsAdapter.FormsAdapter
