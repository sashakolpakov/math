import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomologyPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamSheafificationUnit

/-! # Homology Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.HomologyPresheaf

noncomputable section

/-! Canonical comparison from original de Rham presheaf homology to coherent Frobenius homology. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable (k : Type u) [Field k] [Fintype k] (X : Over (Spec (CommRingCat.of k)))

def underlyingComplex : CochainComplex (X.left.Opensᵒᵖ ⥤ ModuleCat.{u} k) ℕ :=
  ((Affine.HomologyPresheaf.functor k X).mapHomologicalComplex (.up ℕ)).obj
    (DeRhamGlobal.complex k X)

def underlyingIso : underlyingComplex k X ≅ DeRhamCechTotal.presheafComplex k X :=
  ((DeRhamCechTotal.presheaves k X).mapHomologicalComplex (.up ℕ)).mapIso
    (DeRhamSheafIso.iso k X)

def sheafHomology (n : ℕ) : X.left.Opensᵒᵖ ⥤ ModuleCat.{u} k :=
  (Affine.HomologyPresheaf.functor k X).obj ((DeRhamGlobal.complex k X).homology n)

def comparison (n : ℕ) : (underlyingComplex k X).homology n ⟶ sheafHomology k X n :=
  Affine.HomologyPresheaf.map k X ((DeRhamGlobal.complex k X).sc n)

def rawMap : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k X ⟶ underlyingComplex k X :=
  DeRhamSheafificationUnit.map k X ≫ (underlyingIso k X).inv

def rawHomologyMap (n : ℕ) : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k X).homology n ⟶ sheafHomology k X n :=
  HomologicalComplex.homologyMap (rawMap k X) n ≫ comparison k X n

variable [IsProper X.hom] [Smooth X.hom]

theorem affine_comparison_isIso (U : X.left.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    IsIso ((comparison k X n).app (op U)) := by
  exact @Affine.HomologyPresheaf.affine_isIso k inferInstance X
    ((DeRhamGlobal.complex k X).sc n)
    (SmoothProper.FrobeniusCoherence.quasicoherent k X ((ComplexShape.up ℕ).prev n))
    (SmoothProper.FrobeniusCoherence.quasicoherent k X n)
    (SmoothProper.FrobeniusCoherence.quasicoherent k X ((ComplexShape.up ℕ).next n)) U hU

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.HomologyPresheaf
