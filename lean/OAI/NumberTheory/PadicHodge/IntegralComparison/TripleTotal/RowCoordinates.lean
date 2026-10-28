import OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RotationInjection

/-! # Row Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RowCoordinates

noncomputable section

/-! The other grouping is the actual outer complex of row totals.
Finite-coproduct evaluation gives the canonical coordinate isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A] [HasFiniteCoproducts A]
attribute [local instance] Rotation.total Rotation.complexTotal
  Rotation.flipZero Components.totalAdditive

local instance flipAdditive :
    (HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).Additive where
  map_add := by
    intros
    ext i j
    rfl

def rowFunctor : HomologicalComplex₂ A (.up ℕ) (.up ℕ) ⥤ CochainComplex A ℕ :=
  HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)

instance rowAdditive : (rowFunctor (A := A)).Additive := by
  dsimp only [rowFunctor]
  infer_instance

variable (S : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ))

def bicomplex : HomologicalComplex₂ A (.up ℕ) (.up ℕ) :=
  HomologicalComplex₂.flip
    (((rowFunctor (A := A)).mapHomologicalComplex (.up ℕ)).obj (HomologicalComplex₂.flip S))

def rowIso (j : ℕ) : ((HomologicalComplex₂.flip (bicomplex S)).X j) ≅
    (HomologicalComplex₂.flip (Components.leftBicomplex
      (Rotation.rotate S))).X j :=
  AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso (HomologicalComplex.eval A (.up ℕ) j)
    (Rotation.rotate S)

def flippedMap : HomologicalComplex₂.flip (bicomplex S) ⟶
    HomologicalComplex₂.flip (Components.leftBicomplex
      (Rotation.rotate S)) where
  f j := (rowIso S j).hom
  comm' j j' _ :=
    (GeometricComparison.Finite.TotalTransformation.FiniteTotalTransformation.naturality
      (HomologicalComplex.dNatTrans A (.up ℕ) j j') (Rotation.rotate S)).symm

instance flippedMap_isIso : IsIso (flippedMap S) := by
  let : ∀ j, IsIso ((flippedMap S).f j) := fun j => inferInstanceAs (IsIso (rowIso S j).hom)
  exact HomologicalComplex.Hom.isIso_of_components _

def bicomplexIso : bicomplex S ≅
    Components.leftBicomplex (Rotation.rotate S) :=
  (HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).mapIso (asIso (flippedMap S))

def totalIso : (bicomplex S).total (.up ℕ) ≅
    Components.left (Rotation.rotate S) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso S) (.up ℕ)

def regroup : (HomologicalComplex₂.flip (S.total (.up ℕ))).total (.up ℕ) ⟶
    (bicomplex S).total (.up ℕ) :=
  Rotation.regroup S ≫ (totalIso S).inv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RowCoordinates
