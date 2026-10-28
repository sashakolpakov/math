import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoordinateLinearity

/-! # Relative Forms Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeFormsFunctor.CoordinateForms

noncomputable section

/-! Relative forms carry the fixed coordinate-base module structure needed for affine Čech descent. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

@[instance_reducible]
def baseAlgebra (B : CommAlgCat.{u} A) : Algebra R B :=
  ((algebraMap A B).comp (algebraMap R A)).toAlgebra

abbrev restrictAlg (B : CommAlgCat.{u} A) : CommAlgCat.{u} R := by
  letI := baseAlgebra R A B
  exact CommAlgCat.of R B

local instance coordinateAlgebra (B : CommAlgCat.{u} A) : Algebra A (restrictAlg R A B) :=
  B.algebra

def restrictAlgMap {B C : CommAlgCat.{u} A} (f : B ⟶ C) :
    restrictAlg R A B ⟶ restrictAlg R A C := by
  letI := baseAlgebra R A B
  letI := baseAlgebra R A C
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact CommAlgCat.ofHom (f.hom.restrictScalars R)

def formMap {B C : CommAlgCat.{u} A} (f : B ⟶ C) (n : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (restrictAlg R A B) n →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (restrictAlg R A C) n where
  toFun := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (restrictAlgMap R A f) n
  map_add' := map_add _
  map_smul' a ω := by
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (restrictAlgMap R A f) n (a • ω) =
      a • AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (restrictAlgMap R A f) n ω
    rw [← IsScalarTower.algebraMap_smul (restrictAlg R A B) a ω, Forms.CoordinateLinearity.FormsBaseChange.formMap_smul]
    have h : (restrictAlgMap R A f) (algebraMap A B a) = algebraMap A C a := f.hom.commutes a
    rw [h, IsScalarTower.algebraMap_smul]

theorem formMap_symbol {B C : CommAlgCat.{u} A} (f : B ⟶ C) (n : ℕ) (b : B) (v : Fin n → B) :
    formMap R A f n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (restrictAlg R A B) b v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (restrictAlg R A C) (f b) (fun i => f (v i)) := by
  change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (restrictAlgMap R A f) n
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (restrictAlg R A B) b v) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol]
  rfl

def functor (n : ℕ) : CommAlgCat.{u} A ⥤ ModuleCat.{u} A where
  obj B := ModuleCat.of A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (restrictAlg R A B) n)
  map f := ModuleCat.ofHom (formMap R A f n)
  map_id B := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_id (restrictAlg R A B) n)
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_comp
      (restrictAlgMap R A f) (restrictAlgMap R A g) n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeFormsFunctor.CoordinateForms
