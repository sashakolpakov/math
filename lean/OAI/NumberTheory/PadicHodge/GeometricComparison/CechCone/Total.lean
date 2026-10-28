import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Augmentation
import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists
import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total.CechConeTotal

noncomputable section

/-! A natural cone of actual complexes gives its canonical augmentation
into the Čech total complex, with the original two differentials. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v w z t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Preadditive A] [HasProducts.{t} A]
  {ι : Type t} (U : ι → C) (P : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (M : CochainComplex A ℕ) (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

def horizontal : HomologicalComplex₂ A (.up ℕ) (.up ℕ) :=
  (IntegralComparison.NonemptyCechNerve.complexFunctor U).obj P

def bicomplex : HomologicalComplex₂ A (.up ℕ) (.up ℕ) := (horizontal U P).flip

def zeroMap : M ⟶ (horizontal U P).X 0 := (NonemptyCech.Augmentation.NonemptyCechAugmentation.restriction U P M η).app ⦋0⦌

def component (q : ℕ) : M.X q ⟶ ((CechConeTotal.bicomplex U P).X q).X 0 := (zeroMap U P M η).f q

theorem comm (q q' : ℕ) : component U P M η q ≫ ((CechConeTotal.bicomplex U P).d q q').f 0 =
    M.d q q' ≫ component U P M η q' := (zeroMap U P M η).comm q q'

theorem cocycle (q : ℕ) : component U P M η q ≫ ((CechConeTotal.bicomplex U P).X q).d 0 1 = 0 :=
  congrArg (fun α : M ⟶ (horizontal U P).X 1 => α.f q)
    (NonemptyCech.Augmentation.NonemptyCechAugmentation.cocycle U P M η)

variable [HasFiniteCoproducts A]

local instance hasTotal : (CechConeTotal.bicomplex U P).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def total : CochainComplex A ℕ := (CechConeTotal.bicomplex U P).total (.up ℕ)

def augmentation : M ⟶ CechConeTotal.total U P :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (bicomplex U P)) M (component U P M η)
    (fun q q' _ => CechConeTotal.comm U P M η q q') (cocycle U P M η)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total.CechConeTotal
