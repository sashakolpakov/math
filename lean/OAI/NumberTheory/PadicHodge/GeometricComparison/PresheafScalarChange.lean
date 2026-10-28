import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarFormsChange

/-! # Presheaf Scalar Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafScalarChange.SectionScalarChange

noncomputable section

/-! Change of coefficients on the native presheaf de Rham complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)

def semilinearModuleIso {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] (e : M ≃ₛₗ[σ.toRingHom] N) :
    ModuleCat.of R M ≅
      (ModuleCat.restrictScalars σ.toRingHom).obj (ModuleCat.of S N) := by
  letI : Module R N := Module.compHom N σ.toRingHom
  exact (show M ≃ₗ[R] N from
    { __ := e.toAddEquiv
      map_smul' := e.map_smul' }).toModuleIso

variable (X : Over (Spec (CommRingCat.of S)))

def sectionFormsIso (U : X.left.Opens) (n : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) n).obj (.op U) ≅
      (ModuleCat.restrictScalars σ.toRingHom).obj
        ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S X n).obj (.op U)) := by
  letI : Algebra R Γ(X.left, U) :=
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) U
  letI : Algebra S Γ(X.left, U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X U
  exact semilinearModuleIso σ
    (ScalarFormsChange.FormsScalarChange.semilinearEquiv (A := Γ(X.left, U)) σ
      (ScalarFormsChange.SectionScalarChange.sectionBaseMap_comp σ.toRingHom X U) n)

def formsPresheafIso (n : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) n ≅
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S X n ⋙ ModuleCat.restrictScalars σ.toRingHom :=
  NatIso.ofComponents (fun U => sectionFormsIso σ X U.unop n) (by
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    let : Algebra R Γ(X.left, U.unop) :=
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) U.unop
    let : Algebra S Γ(X.left, U.unop) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X U.unop
    let : Algebra R Γ(X.left, V.unop) :=
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) V.unop
    let : Algebra S Γ(X.left, V.unop) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X V.unop
    exact ScalarFormsChange.FormsScalarChange.formEquiv_naturality (A := Γ(X.left, U.unop))
      (B := Γ(X.left, V.unop)) σ
      (ScalarFormsChange.SectionScalarChange.sectionBaseMap_comp σ.toRingHom X U.unop)
      (ScalarFormsChange.SectionScalarChange.sectionBaseMap_comp σ.toRingHom X V.unop)
      ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)).map f)
      ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras S X).map f) (fun _ => rfl) n ω)

abbrev presheafRestriction :
    (X.left.Opensᵒᵖ ⥤ ModuleCat S) ⥤ (X.left.Opensᵒᵖ ⥤ ModuleCat R) :=
  (Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars σ.toRingHom)

def presheafComplexIso :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) ≅
      ((presheafRestriction σ X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S X) :=
  HomologicalComplex.Hom.isoOfComponents (formsPresheafIso σ X) (by
    intro i j hij
    obtain rfl := (show i + 1 = j from hij)
    change (formsPresheafIso σ X i).hom ≫
        (presheafRestriction σ X).map ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S X).d i (i + 1)) =
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)).d i (i + 1) ≫
        (formsPresheafIso σ X (i + 1)).hom
    rw [show (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S X).d i (i + 1) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf S X i from CochainComplex.of_d _ _ i]
    rw [show (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)).d i (i + 1) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) i from
        CochainComplex.of_d _ _ i]
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    let : Algebra R Γ(X.left, U.unop) :=
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) U.unop
    let : Algebra S Γ(X.left, U.unop) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X U.unop
    exact (ScalarFormsChange.FormsScalarChange.semilinearEquiv_differential (A := Γ(X.left, U.unop)) σ
      (ScalarFormsChange.SectionScalarChange.sectionBaseMap_comp σ.toRingHom X U.unop) i ω).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafScalarChange.SectionScalarChange
