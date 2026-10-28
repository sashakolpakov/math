import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterTensorIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ParameterFunctoriality

/-! # Product Comparison Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.ProductComparisonNaturality

noncomputable section

/-! The Cartesian tensor comparison for family pullbacks is natural across parameter maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} {U T : Over S} (f : U ⟶ T) (A B : Over S)

theorem familyProductComparison_geometric_natural :
    (Functor.Monoidal.μIso (Over.pullback U.hom) A B).hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap f (A ⊗ B) =
      Product.ParameterBaseChange.productParameterBaseChangeMap f A B ≫ (Functor.Monoidal.μIso (Over.pullback T.hom) A B).hom.left := by
  apply (IsPullback.of_hasPullback (A ⊗ B).hom T.hom).hom_ext
  · rw [Category.assoc, Single.ParameterBaseChange.singleParameterBaseChangeMap_comp, Category.assoc]
    change Graph.FamilyNaturality.overProductBaseChangeMap U.hom A B = Product.ParameterBaseChange.productParameterBaseChangeMap f A B ≫ Graph.FamilyNaturality.overProductBaseChangeMap T.hom A B
    exact (Product.ParameterBaseChange.productParameterBaseChangeMap_comp f A B).symm
  · change ((Functor.Monoidal.μIso (Over.pullback U.hom) A B).hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap f (A ⊗ B)) ≫
        ((Over.pullback T.hom).obj (A ⊗ B)).hom =
      (Product.ParameterBaseChange.productParameterBaseChangeMap f A B ≫ (Functor.Monoidal.μIso (Over.pullback T.hom) A B).hom.left) ≫
        ((Over.pullback T.hom).obj (A ⊗ B)).hom
    rw [Category.assoc, Single.ParameterFunctoriality.singleParameterBaseChangeMap_over, ← Category.assoc,
      (Functor.Monoidal.μIso (Over.pullback U.hom) A B).hom.w, Category.assoc,
      (Functor.Monoidal.μIso (Over.pullback T.hom) A B).hom.w, Product.ParameterBaseChange.productParameterBaseChangeMap_over]

theorem familyProductComparison_natural :
    (Functor.Monoidal.μIso (Over.pullback U.hom) A B).hom ≫ (Single.ParameterBaseChange.singleParameterBaseChangeIso f (A ⊗ B)).hom =
      (Product.ParameterBaseChange.productParameterBaseChangeIso f A B).hom ≫
        (Over.pullback f.left).map (Functor.Monoidal.μIso (Over.pullback T.hom) A B).hom :=
  (Cartesian.OverIsoNaturality.cartesianAmbientOverIso_natural f.left (Product.ParameterBaseChange.productParameterBaseChangeMap f A B)
    (Single.ParameterBaseChange.singleParameterBaseChangeMap f (A ⊗ B))
    (Product.ParameterBaseChange.productParameterBaseChangeMap_isPullback f A B) (Single.ParameterBaseChange.singleParameterBaseChangeMap_isPullback f (A ⊗ B))
    (Functor.Monoidal.μIso (Over.pullback U.hom) A B).hom
    (Functor.Monoidal.μIso (Over.pullback T.hom) A B).hom
    (familyProductComparison_geometric_natural f A B).symm).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.ProductComparisonNaturality
