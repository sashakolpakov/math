import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryReductionProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct

/-! # Ordinary Quotient Diagram Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary

noncomputable section

/-! The actual coefficient quotient of an ordinary de Rham diagram has
its induced integral wedge and its native Čech cohomology product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction
universe u v w
variable (R : Type u) [CommRing R] (I : Ideal R)
  {C : Type v} [Category.{w} C] (A : Cᵒᵖ ⥤ CommAlgCat.{u} R)

def diagram := A ⋙ OrdinaryDeRhamFunctor.Ordinary.functor R ⋙
  (Module.IdealQuotient.functor R I).mapHomologicalComplex (.up ℕ)
abbrev complex := Cech.ComplexDiagramCoordinates.complex (diagram R I A)

def pairing (i j : ℕ) (V : Cᵒᵖ) :
    ((complex R I A).X i).obj V →ₗ[R] ((complex R I A).X j).obj V →ₗ[R]
      ((complex R I A).X (i+j)).obj V := OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.quotientPairing R I (A.obj V) i j

theorem natural (i j : ℕ) {V W : Cᵒᵖ} (f : V ⟶ W)
    (x : ((complex R I A).X i).obj V) (y : ((complex R I A).X j).obj V) :
    ((complex R I A).X (i+j)).map f (pairing R I A i j V x y) =
      pairing R I A i j W (((complex R I A).X i).map f x) (((complex R I A).X j).map f y) :=
  Module.IdealQuotientProduct.pairing_natural I (OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.ordinaryPairing R (A.obj V) i j)
    (OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.ordinaryPairing R (A.obj W) i j)
    ((OrdinaryDeRhamFunctor.Ordinary.map (A.map f)).f i)
    ((OrdinaryDeRhamFunctor.Ordinary.map (A.map f)).f j)
    ((OrdinaryDeRhamFunctor.Ordinary.map (A.map f)).f (i+j))
    (IntegralDeRham.WedgeNaturality.formMap_wedge (A.map f) i j) x y

private theorem ordinary_d_apply (B : CommAlgCat.{u} R) (i : ℕ)
    (x : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B).X i) :
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B).d i (i+1) x = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R B i x := by
  simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex, CochainComplex.of_d]
  rfl

private theorem ordinary_cupInto (B : CommAlgCat.{u} R) (i j l : ℕ) (h : i+j=l)
    (x : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B).X i) (y : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B).X j) :
    Cochain.CohomologyCup.cupInto (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B)
        (OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.ordinaryPairing R B) i j l h x y =
      IntegralDeRham.WedgeSigns.degreeCast R B h (IntegralDeRham.DeRhamWedge.wedge R B i j x y) := by
  subst l
  rfl

private theorem ordinary_differential (B : CommAlgCat.{u} R) (i j : ℕ)
    (x : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B).X i) (y : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B).X j) :
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B).d (i+j) (i+j+1) (OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.ordinaryPairing R B i j x y) =
      Cochain.CohomologyCup.cupInto (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B) (OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.ordinaryPairing R B)
        (i+1) j (i+j+1) (by omega) ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B).d i (i+1) x) y +
      (-1 : ℤ)^i • Cochain.CohomologyCup.cupInto (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B)
        (OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.ordinaryPairing R B) i (j+1) (i+j+1) (by omega)
        x ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B).d j (j+1) y) := by
  rw [ordinary_d_apply, ordinary_cupInto, ordinary_cupInto, ordinary_d_apply, ordinary_d_apply]
  exact IntegralDeRham.Leibniz.Wedge.differential_wedge R B i j x y

private theorem quotient_cupInto (i j l : ℕ) (h : i+j=l) (V : Cᵒᵖ)
    (x : ((complex R I A).X i).obj V) (y : ((complex R I A).X j).obj V) :
    Cochain.CohomologyCup.cupInto
        (Module.IdealQuotient.complex R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R (A.obj V)))
        (OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.quotientPairing R I (A.obj V)) i j l h x y =
      Presheaf.CechProduct.sectionDegreeCast (complex R I A) h V
        (pairing R I A i j V x y) := by
  subst l
  rfl

theorem differential (i j : ℕ) (V : Cᵒᵖ)
    (x : ((complex R I A).X i).obj V) (y : ((complex R I A).X j).obj V) :
    ((complex R I A).d (i+j) (i+j+1)).app V (pairing R I A i j V x y) =
      Presheaf.CechProduct.sectionDegreeCast (complex R I A) (by omega) V
        (pairing R I A (i+1) j V (((complex R I A).d i (i+1)).app V x) y) +
      (-1 : ℤ)^i • Presheaf.CechProduct.sectionDegreeCast (complex R I A) (by omega) V
        (pairing R I A i (j+1) V x (((complex R I A).d j (j+1)).app V y)) := by
  have h := IdealQuotientCochainProduct.Module.differential_complexPairing I
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R (A.obj V)) (OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.ordinaryPairing R (A.obj V))
    (ordinary_differential R (A.obj V)) i j x y
  exact h.trans (congrArg₂
    (fun x y : ((complex R I A).X (i+j+1)).obj V => x+y)
    (quotient_cupInto R I A (i+1) j (i+j+1) (by omega) V
      (((complex R I A).d i (i+1)).app V x) y)
    (congrArg (fun z : ((complex R I A).X (i+j+1)).obj V => (-1 : ℤ)^i • z)
      (quotient_cupInto R I A i (j+1) (i+j+1) (by omega) V
        x (((complex R I A).d j (j+1)).app V y))))

variable [HasBinaryProducts C] {ι : Type} [Finite ι] (U : ι → C)
abbrev total := Presheaf.TotalCup.CechProduct.total (NonemptyCechNerve.nerve U) (complex R I A)
abbrev cup := Presheaf.TotalCup.CechProduct.totalCup (NonemptyCechNerve.nerve U)
  (complex R I A) (pairing R I A)
abbrev cohomologyCup := Presheaf.CohomologyProduct.Cech.cohomologyCup (NonemptyCechNerve.nerve U)
  (complex R I A) (pairing R I A) (natural R I A) (differential R I A)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary
