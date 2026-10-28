import OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticComplexDiagrams
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarFactorBaseChange

/-! # Scalar Factor Pair -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarFactorPair.ScalarFactorDiagram

noncomputable section

/-! A finite diagram containing the original abelian variety, its
scalar factors, both splitting maps, and every integral basis action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {n r g : ℕ} {d : Fin n → ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (B : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) Foundations.Scheme.ProjectiveSpace.complexBase)

def dimension : Fin (n + 1) → ℕ := Fin.cases g d

def abelian : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (ScalarFactorDiagram.dimension (g := g) (d := d) i) Foundations.Scheme.ProjectiveSpace.complexBase :=
  Fin.cases A B

def sourcePair (i : Fin n) (k : Fin (r + 2)) : Fin (n + 1) :=
  Fin.cases 0 (fun _ => i.succ) k

def targetPair (i : Fin n) (k : Fin (r + 2)) : Fin (n + 1) :=
  Fin.cases i.succ (Fin.cases 0 (fun _ => i.succ)) k

def source (a : Fin (n * (r + 2))) : Fin (n + 1) :=
  sourcePair (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2

def target (a : Fin (n * (r + 2))) : Fin (n + 1) :=
  targetPair (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2

variable (D : TorsionFactorIso.AbelianScalarFactorization A B)
  {O : Type*} [CommRing O] (basis : Module.Basis (Fin r) ℤ O)
  (action : ∀ i, AbelianModuli.ReferenceFamily.ActionData.IntegralAction O (B i))

def mapPair (i : Fin n) (k : Fin (r + 2)) :
    (ScalarFactorDiagram.abelian A B (sourcePair i k)).scheme ⟶ (ScalarFactorDiagram.abelian A B (targetPair i k)).scheme := by
  dsimp only [sourcePair, targetPair]
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun j => ?_) k) k
  · exact D.forward i
  · exact D.backward i
  · exact (action i).map (basis j)

theorem mapPair_group (i : Fin n) (k : Fin (r + 2)) : IsMonHom (mapPair A B D basis action i k) := by
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun j => ?_) k) k
  · exact D.forward_group i
  · exact D.backward_group i
  · exact (action i).preservesGroup (basis j)

def map (a : Fin (n * (r + 2))) :
    (ScalarFactorDiagram.abelian A B (ScalarFactorDiagram.source a)).scheme ⟶ (ScalarFactorDiagram.abelian A B (ScalarFactorDiagram.target a)).scheme :=
  mapPair A B D basis action (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2

theorem map_group (a : Fin (n * (r + 2))) : IsMonHom (ScalarFactorDiagram.map A B D basis action a) :=
  mapPair_group A B D basis action _ _

def diagram : ArithmeticComplexDiagrams.FiniteComplexAbelianDiagram where
  objects := n + 1
  arrows := n * (r + 2)
  dimension := ScalarFactorDiagram.dimension (g := g) (d := d)
  abelian := ScalarFactorDiagram.abelian A B
  source := ScalarFactorDiagram.source
  target := ScalarFactorDiagram.target
  map := ScalarFactorDiagram.map A B D basis action
  group := map_group A B D basis action

def models (M : AbelianArithmeticModels.AbelianNumberFieldModel A) (N : ∀ i, AbelianArithmeticModels.AbelianNumberFieldModel (B i)) :
    ∀ i, AbelianArithmeticModels.AbelianNumberFieldModel ((diagram A B D basis action).abelian i) :=
  Fin.cases M N

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarFactorPair.ScalarFactorDiagram
