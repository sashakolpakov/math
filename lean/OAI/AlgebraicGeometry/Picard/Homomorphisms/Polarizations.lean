import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualData
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPolarization
import OAI.AlgebraicGeometry.Picard.Homomorphisms.AbelianSchemes
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf

/-! # Polarizations -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Polarizations

noncomputable section

/-! Polarizations of the geometric abelian-scheme bundle. The dual group
law is constructed from Picard tensor product. Positivity is the actual
ample-line-bundle Poincare formula on every geometric fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} (A : AbelianSchemes.Construction.AbelianScheme S)

def PositiveOnGeometricFiber (D : UnbundledDualData.Construction.UnbundledPicard.DualData A.toOver)
    (ell : A.toOver ⟶ D.abelian) (k : Type u) [Field k] [IsAlgClosed k]
    (s : Spec (.of k) ⟶ S) : Prop :=
  let B := (Over.pullback s).obj A.toOver
  let P := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (((Over.pullback s).map ell ⊗ₘ 𝟙 B).left) (D.pullback s).poincare
  ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left, L.IsAmple ∧
    Nonempty ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback η[B].left L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of k))) ∧
    Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule P.sheaf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (fst B B).left L).sheaf)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (snd B B).left L).sheaf ≅
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback μ[B].left L).sheaf)

structure Polarization where
  representation : UnbundledDualData.Construction.UnbundledPicard.DualData A.toOver
  map : A.toOver ⟶ representation.withPicardGroup.abelian
  preservesGroup : IsMonHom map
  finite : IsFinite map.left
  flat : Flat map.left
  surjective : Surjective map.left
  positive : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
    PositiveOnGeometricFiber A representation.withPicardGroup map k s

attribute [instance] Polarization.preservesGroup Polarization.finite
  Polarization.flat Polarization.surjective

variable {A}

def Polarization.dual (ell : Polarization A) : UnbundledDualData.Construction.UnbundledPicard.DualData A.toOver :=
  ell.representation.withPicardGroup

def Polarization.hom (ell : Polarization A) : Additive (A.toOver ⟶ ell.dual.abelian) :=
  Additive.ofMul ell.map

theorem Polarization.dual_group_eq_picard (ell : Polarization A) :
    ell.dual.group = UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup ell.dual :=
  UnbundledDualData.Construction.UnbundledPicard.DualData.withPicardGroup_group ell.representation

def Polarization.frobeniusTwist (ell : Polarization A)
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) :
    Frobenius.Construction.frobeniusTwist p hp hS A.toOver ⟶
      (ell.dual.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).abelian :=
  (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map ell.map

/-- Pullback is the actual composite F∨ ∘ λ^(p) ∘ F, in additive notation. -/
def pullbackPolarizationHom (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)
    (ell : Polarization A) : Additive (A.toOver ⟶ ell.dual.abelian) :=
  Additive.ofMul (Frobenius.Construction.relativeFrobenius p hp hS A.toOver ≫ ell.frobeniusTwist p hp hS ≫
    UnbundledDualFrobenius.Construction.UnbundledPicard.dualRelativeFrobenius ell.dual p hp hS)

theorem frobenius_pullback_polarization (p : ℕ) (hp : p.Prime)
    (hS : (p : Γ(S, ⊤)) = 0) (ell : Polarization A) :
    pullbackPolarizationHom p hp hS ell = p • ell.hom := by
  have h := UnbundledPolarization.Construction.UnbundledPicard.frobenius_pullback_picardGroup_nsmul ell.dual p hp hS ell.map
  rw [← ell.dual_group_eq_picard] at h
  exact h

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Polarizations
