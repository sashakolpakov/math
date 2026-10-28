import OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Association
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalTransformation

/-! # Rotation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Rotation

noncomputable section

/-! Evaluation in the coefficient degree identifies the native
Čech-first grouping with the corresponding right-bracketed triple
total. This is the actual finite coproduct comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A] [HasFiniteCoproducts A]

local instance total (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance complexTotal (K : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

local instance flipZero :
    (HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).PreservesZeroMorphisms where
  map_zero := by
    intros
    ext i j
    rfl

variable (S : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ))

def rotate : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ) :=
  HomologicalComplex₂.flip
    (((HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj S)

def rowIso (r : ℕ) : (Components.rightBicomplex (rotate S)).X r ≅
    (HomologicalComplex₂.flip (S.total (.up ℕ))).X r :=
  AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso (HomologicalComplex.eval A (.up ℕ) r) S

def bicomplexMap : Components.rightBicomplex (rotate S) ⟶
    HomologicalComplex₂.flip (S.total (.up ℕ)) where
  f r := (rowIso S r).hom
  comm' r r' _ :=
    (GeometricComparison.Finite.TotalTransformation.FiniteTotalTransformation.naturality (HomologicalComplex.dNatTrans A (.up ℕ) r r') S).symm

instance bicomplexMap_isIso : IsIso (bicomplexMap S) := by
  let : ∀ r, IsIso ((bicomplexMap S).f r) := fun r =>
    inferInstanceAs (IsIso (rowIso S r).hom)
  exact HomologicalComplex.Hom.isIso_of_components _

def bicomplexIso : Components.rightBicomplex (rotate S) ≅
    HomologicalComplex₂.flip (S.total (.up ℕ)) := asIso (bicomplexMap S)

def totalIso : Components.right (rotate S) ≅
    (HomologicalComplex₂.flip (S.total (.up ℕ))).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso S) (.up ℕ)

def regroup : (HomologicalComplex₂.flip (S.total (.up ℕ))).total (.up ℕ) ⟶
    Components.left (rotate S) :=
  (totalIso S).inv ≫ Association.map (rotate S)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Rotation
