import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId

/-! # Cech Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct

noncomputable section

/-! The integral symbol product on the original ordinary de Rham
presheaf and its actual Čech total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X

def sectionPairing (a b : ℕ) (U : X.left.Opensᵒᵖ) :
    ((P).X a).obj U →ₗ[R] ((P).X b).obj U →ₗ[R] ((P).X (a + b)).obj U :=
  (DeRhamWedge.wedge R Γ(X.left, U.unop) a b).restrictScalars₁₂ R R

theorem sectionPairing_natural (a b : ℕ) {U V : X.left.Opensᵒᵖ} (f : U ⟶ V)
    (x : ((P).X a).obj U) (y : ((P).X b).obj U) :
    ((P).X (a + b)).map f (sectionPairing R X a b U x y) =
      sectionPairing R X a b V (((P).X a).map f x) (((P).X b).map f y) :=
  WedgeNaturality.formMap_wedge ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map f) a b x y

theorem sectionPairing_apply (a b : ℕ) (U : X.left.Opensᵒᵖ)
    (x : ((P).X a).obj U) (y : ((P).X b).obj U) :
    sectionPairing R X a b U x y = DeRhamWedge.wedge R Γ(X.left, U.unop) a b x y := rfl

theorem differential_apply (a : ℕ) (U : X.left.Opensᵒᵖ) (x : ((P).X a).obj U) :
    ((P).d a (a + 1)).app U x = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R Γ(X.left, U.unop) a x := by
  exact congrArg (fun d : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X a ⟶
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X (a + 1) => d.app U x)
      (CochainComplex.of_d (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X)
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X) a)

theorem sectionDegreeCast_apply {a b : ℕ} (e : a = b) (U : X.left.Opensᵒᵖ)
    (x : ((P).X a).obj U) :
    Presheaf.CechProduct.sectionDegreeCast P e U x =
      WedgeSigns.degreeCast R Γ(X.left, U.unop) e x := by
  subst b
  rfl

theorem sectionPairing_differential (a b : ℕ) (U : X.left.Opensᵒᵖ)
    (x : ((P).X a).obj U) (y : ((P).X b).obj U) :
    ((P).d (a + b) (a + b + 1)).app U (sectionPairing R X a b U x y) =
      Presheaf.CechProduct.sectionDegreeCast P (by omega : (a + 1) + b = a + b + 1) U
        (sectionPairing R X (a + 1) b U (((P).d a (a + 1)).app U x) y) +
      (-1 : ℤ) ^ a • Presheaf.CechProduct.sectionDegreeCast P
        (by omega : a + (b + 1) = a + b + 1) U
        (sectionPairing R X a (b + 1) U x (((P).d b (b + 1)).app U y)) := by
  have hproduct := @Leibniz.Wedge.differential_wedge R Γ(X.left, U.unop) _ _
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U.unop) a b x y
  rw [differential_apply, sectionPairing_apply,
    sectionDegreeCast_apply, sectionDegreeCast_apply,
    sectionPairing_apply, sectionPairing_apply, differential_apply, differential_apply]
  exact hproduct

variable (N : SimplicialObject (FormalCoproduct.{u} X.left.Opens))

def total : CochainComplex (ModuleCat.{u} R) ℕ := Presheaf.TotalCup.CechProduct.total N P

def totalCup (a b : ℕ) :
    (total R X N).X a →ₗ[R] (total R X N).X b →ₗ[R] (total R X N).X (a + b) :=
  Presheaf.TotalCup.CechProduct.totalCup N P (sectionPairing R X) a b

def cohomologyCup (a b : ℕ) :
    (total R X N).homology a →ₗ[R] (total R X N).homology b →ₗ[R] (total R X N).homology (a + b) := by
  refine Presheaf.CohomologyProduct.Cech.cohomologyCup N P (sectionPairing R X) ?_ ?_ a b
  · intro i j U V f x y
    exact sectionPairing_natural R X i j f x y
  · intro i j U x y
    exact sectionPairing_differential R X i j U x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct
