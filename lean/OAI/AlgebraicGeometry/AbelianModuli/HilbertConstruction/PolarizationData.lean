import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf

/-! # Polarization Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData

noncomputable section

/-!
Concrete polarized abelian data. Positivity is imposed on every geometric
fiber using an ample line bundle and the normalized Poincare formula
`B_lambda ⊗ pr₁*L ⊗ pr₂*L ≅ m*L`. The ample line bundle occurs under an
existential quantifier, so it is not extra chosen moduli data. Polarization
type is the geometric kernel type, intended under the tame hypotheses in HilbertConstruction.
No moduli representability or existence statement is a field.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g : ℕ} {S T : Scheme.{u}} {A : Abelian.Schemes.AbelianScheme g S}

/-- The map from the product of two base changes to the original product. -/
def poincareBaseChangeMap (D : Dual.Data.DualAbelianData A) (s : T ⟶ S) :
    ((D.abelian.pullback s).scheme ⊗ (A.pullback s).scheme).left ⟶
      (D.abelian.scheme ⊗ A.scheme).left :=
  (Functor.Monoidal.μIso (Over.pullback s) D.abelian.scheme A.scheme).hom.left ≫
    CategoryTheory.Limits.pullback.fst (D.abelian.scheme ⊗ A.scheme).hom s

/-- The Poincare bundle pulled back by the candidate polarization on a fiber. -/
def polarizationBiextensionAt (D : Dual.Data.DualAbelianData A)
    (polarizationMap : A.scheme ⟶ D.abelian.scheme) (s : T ⟶ S) :
    Line.Bundles.LineBundle (((A.pullback s).scheme ⊗ (A.pullback s).scheme).left) :=
  Line.Bundles.LineBundle.pullback
    (((Over.pullback s).map polarizationMap ⊗ₘ 𝟙 (A.pullback s).scheme).left ≫
      poincareBaseChangeMap D s) D.poincare

/-- The isogeny on a geometric fiber is induced by an ample line bundle.
The normalization at the identity removes the one-dimensional scalar factor
in the Poincare formula. -/
def PositiveOnGeometricFiber (D : Dual.Data.DualAbelianData A)
    (polarizationMap : A.scheme ⟶ D.abelian.scheme)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S) : Prop :=
  let B := (A.pullback s).scheme
  ∃ L : Line.Bundles.LineBundle B.left,
    L.IsAmple ∧
    Nonempty ((Line.Bundles.LineBundle.pullback η[B].left L).sheaf ≅
      Line.Bundles.structureModule (Spec (.of K))) ∧
    Nonempty
      (Tensor.ProductSheaf.tensorModule
        (Tensor.ProductSheaf.tensorModule (polarizationBiextensionAt D polarizationMap s).sheaf
          (Line.Bundles.LineBundle.pullback (fst B B).left L).sheaf)
        (Line.Bundles.LineBundle.pullback (snd B B).left L).sheaf ≅
        (Line.Bundles.LineBundle.pullback μ[B].left L).sheaf)

/-- A polarization of the specified type, relative to the dual Poincare data. -/
structure Polarization (D : Dual.Data.DualAbelianData A) (δ : Fin g → ℕ) where
  isogeny : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian
  kernelType : isogeny.HasPolarizationType δ
  positive : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
    PositiveOnGeometricFiber D isogeny.hom K s

/-- Polarized abelian schemes with the arbitrary ordered full levels of HilbertConstruction. -/
structure PolarizedAbelianWithFullLevel (g : ℕ) (δ : Fin g → ℕ) (N : ℕ)
    (S : Scheme.{u}) where
  abelian : Abelian.Schemes.AbelianScheme g S
  dual : Dual.Data.DualAbelianData abelian
  polarization : Polarization dual δ
  level : abelian.FullLevel N

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData
