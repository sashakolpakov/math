import OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamCechTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusSheafificationUnit

/-! # De Rham Sheafification Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamSheafificationUnit

noncomputable section

/-! The canonical complex map from actual de Rham presheaves to their sheafification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k : Type u) [Field k] [Fintype k] (X : Over (Spec (CommRingCat.of k)))

def map : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k X ⟶ DeRhamCechTotal.presheafComplex k X where
  f n := toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k X n)
  comm' n m _ := (toSheafify_naturality (Opens.grothendieckTopology X.left)
    ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k X).d n m)).symm

def evaluation (U : X.left.Opens) :=
  ((CategoryTheory.evaluation X.left.Opensᵒᵖ (ModuleCat.{u} k)).obj (op U)).mapHomologicalComplex (.up ℕ)

def evaluatedMap (U : X.left.Opens) := (DeRhamSheafificationUnit.evaluation k X U).map (DeRhamSheafificationUnit.map k X)

variable (C σ : Type u) [CommRing C] [Algebra k C] [LinearOrder σ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]
  [Algebra.FormallyEtale (MvPolynomial σ k) C]

include σ in
theorem affine_principal_isIso (c : C) :
    IsIso (evaluatedMap k (Crystalline.Presentation.affineScheme k C) (PrimeSpectrum.basicOpen c)) := by
  have (n : ℕ) : IsIso ((evaluatedMap k (Crystalline.Presentation.affineScheme k C)
      (PrimeSpectrum.basicOpen c)).f n) := Affine.FrobeniusSheafificationUnit.forms_principal k C σ c n
  exact HomologicalComplex.Hom.isIso_of_components _

include σ in
theorem affine_top_isIso : IsIso (evaluatedMap k (Crystalline.Presentation.affineScheme k C) ⊤) := by
  have (n : ℕ) : IsIso ((evaluatedMap k (Crystalline.Presentation.affineScheme k C) ⊤).f n) :=
    Affine.FrobeniusSheafificationUnit.forms_top k C σ n
  exact HomologicalComplex.Hom.isIso_of_components _

def affine_top_iso :
    (DeRhamSheafificationUnit.evaluation k (Crystalline.Presentation.affineScheme k C) ⊤).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k (Crystalline.Presentation.affineScheme k C)) ≅
    (DeRhamSheafificationUnit.evaluation k (Crystalline.Presentation.affineScheme k C) ⊤).obj
      (DeRhamCechTotal.presheafComplex k (Crystalline.Presentation.affineScheme k C)) := by
  let : IsIso (evaluatedMap k (Crystalline.Presentation.affineScheme k C) ⊤) := affine_top_isIso k C σ
  exact asIso (evaluatedMap k (Crystalline.Presentation.affineScheme k C) ⊤)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamSheafificationUnit
