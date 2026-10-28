import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientTransformation
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total

/-! # Complex Diagram Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramCoordinates

noncomputable section

/-! The Čech total of a complex-valued diagram is canonically the
Čech total of the same diagram written degree by degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C) (P : Cᵒᵖ ⥤ CochainComplex A ℕ)

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

def differential (i j : ℕ) : HomologicalComplex.eval A (.up ℕ) i ⟶
    HomologicalComplex.eval A (.up ℕ) j where
  app K := K.d i j
  naturality _ _ f := f.comm i j

def complex : CochainComplex (Cᵒᵖ ⥤ A) ℕ where
  X n := P ⋙ HomologicalComplex.eval A (.up ℕ) n
  d i j := Functor.whiskerLeft P (differential i j)
  shape i j h := by
    apply NatTrans.ext
    funext V
    exact (P.obj V).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext V
    exact (P.obj V).d_comp_d i j k

def rowIso (i : ℕ) : (GeometricComparison.CechCone.Total.CechConeTotal.bicomplex U P).X i ≅
    (CechCoefficient.Total.bicomplex N (complex P)).X i :=
  GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso (HomologicalComplex.eval A (.up ℕ) i) N
    (fun _ => inferInstanceAs (Finite (Fin _ → ι))) P

def bicomplexIso : GeometricComparison.CechCone.Total.CechConeTotal.bicomplex U P ≅
    CechCoefficient.Total.bicomplex N (complex P) :=
  HomologicalComplex.Hom.isoOfComponents (rowIso U P) (fun i j _ =>
    (GeometricComparison.Finite.CechCoefficientTransformation.FiniteCechCoefficientTransformation.complexes
      (HomologicalComplex.eval A (.up ℕ) i) (HomologicalComplex.eval A (.up ℕ) j)
      (differential i j) N (fun _ => inferInstanceAs (Finite (Fin _ → ι))) P).symm)

def totalIso : GeometricComparison.CechCone.Total.CechConeTotal.total U P ≅
    (CechCoefficient.Total.bicomplex N (complex P)).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso U P) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramCoordinates
