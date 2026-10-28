import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientFactor
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.SingleCoefficientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleMapCoordinates

/-! # Principal Top Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopHomology

noncomputable section

/-! The native principal top-form source iso preserves the original
single-degree homology coordinates, including exact additive coefficients. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inv_prefix {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (a : A ⟶ D) (b : B ⟶ D) (h : e.hom ≫ b = a) : e.inv ≫ a = b := by
  rw [← h, Iso.inv_hom_id_assoc]

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (U : X.left.affineOpens) (g : ℕ) [SmoothOfRelativeDimension g X.hom]
  (a : Fin g → Γ(X.left,U.val))

abbrev family := Supported.Comparison.family p k n X U g a
abbrev originalFunctor := PrincipalTopCoordinates.originalFunctor p k n X U ⋙
  AugmentedOrdered.CechFunctor.functor (family p k n X U g a)
abbrev mappedFunctor := PrincipalTopCoordinates.forget p k n X U ⋙
  AugmentedOrdered.CechFunctor.functor (family p k n X U g a)
abbrev coefficient := PrincipalTopSingle.coefficient p k n X U g
abbrev sheafCoefficient := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g
abbrev forget := AdditiveTop.Comparison.forget p k

def originalIso (r : ℕ) := IntegralComparison.Functor.SingleTotal.homologyIso (originalFunctor p k n X U g a)
  (sheafCoefficient p k n X g) g r

def mappedIso (r : ℕ) := IntegralComparison.Functor.SingleTotal.homologyIso (mappedFunctor p k n X U g a)
  (coefficient p k n X U g) g r

def nativeIso (r : ℕ) := IntegralComparison.Functor.SingleTotal.homologyIso
  (AugmentedOrdered.CechFunctor.functor (family p k n X U g a)) (coefficient p k n X U g) g r

def bicomplexMap :
    IntegralComparison.Functor.SingleTotal.bicomplex (originalFunctor p k n X U g a) (sheafCoefficient p k n X g) g ⟶
    IntegralComparison.Functor.SingleTotal.bicomplex (mappedFunctor p k n X U g a) (coefficient p k n X U g) g :=
  ((AugmentedOrdered.CechFunctor.functor (family p k n X U g a)).mapHomologicalComplex (.up ℕ)).map
    (PrincipalTopCoordinates.sourceIso p k n X U g).hom

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem row : (bicomplexMap p k n X U g a).f g ≫
    (IntegralComparison.Functor.SingleTotal.rowIso (mappedFunctor p k n X U g a) (coefficient p k n X U g) g).hom =
    (IntegralComparison.Functor.SingleTotal.rowIso (originalFunctor p k n X U g a) (sheafCoefficient p k n X g) g).hom := by
  have h := congrArg (AugmentedOrdered.CechFunctor.functor (family p k n X U g a)).map
    (PrincipalTopCoordinates.self p k n X U g)
  simpa only [Functor.map_comp, bicomplexMap, IntegralComparison.Functor.SingleTotal.rowIso,
    Functor.mapIso_hom, originalFunctor, mappedFunctor, Functor.comp_map,
    Functor.mapHomologicalComplex_map_f] using h

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem comparison (r : ℕ) :
    homologyMap (AugmentedCech.CoefficientNaturality.Total.totalMap (family p k n X U g a)
      (PrincipalTopCoordinates.sourceIso p k n X U g).hom) (r+g) ≫
      (mappedIso p k n X U g a r).hom = (originalIso p k n X U g a r).hom := by
  have h := IntegralComparison.Functor.SingleMapCoordinates.comparison
    (originalFunctor p k n X U g a) (mappedFunctor p k n X U g a)
    (sheafCoefficient p k n X g) (coefficient p k n X U g) g
    (bicomplexMap p k n X U g a) (𝟙 _)
    (by simpa only [Category.comp_id] using row p k n X U g a) r
  simpa only [homologyMap_id, Category.comp_id, bicomplexMap,
    AugmentedCech.CoefficientNaturality.Total.totalMap, AugmentedCech.CoefficientNaturality.Total.bicomplexMap,
    mappedIso, originalIso] using h

def coefficientIso (r : ℕ) := AugmentedCech.SingleCoefficientCoordinates.coefficientIso
  (family p k n X U g a)
  (𝟭 ((Principal.SectionPresheaf.Index U.val)ᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))))
  (forget p k) (coefficient p k n X U g) r

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem coefficient_comparison (r : ℕ) :
    (AugmentedCech.CoefficientTotal.homologyIso (family p k n X U g a) (forget p k)
      ((single _ (.up ℕ) g).obj (coefficient p k n X U g)) (r+g)).hom ≫
      (mappedIso p k n X U g a r).hom =
    (forget p k).map (nativeIso p k n X U g a r).hom ≫ (coefficientIso p k n X U g a r).hom :=
  AugmentedCech.SingleCoefficientCoordinates.comparison (family p k n X U g a)
    (𝟭 ((Principal.SectionPresheaf.Index U.val)ᵒᵖ ⥤
      ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))))
    (forget p k) (coefficient p k n X U g) g r

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem input_coordinates (r : ℕ) :
    (AugmentedCech.CoefficientFactor.inputIso (family p k n X U g a) (forget p k)
      (PrincipalTopCoordinates.sourceIso p k n X U g) (r+g)).hom ≫
        (originalIso p k n X U g a r).hom =
    (forget p k).map (nativeIso p k n X U g a r).hom ≫ (coefficientIso p k n X U g a r).hom := by
  let e := homologyMapIso
    ((AugmentedCech.CoefficientFactor.totalFunctor (family p k n X U g a)).mapIso
      (PrincipalTopCoordinates.sourceIso p k n X U g)) (r+g)
  have he : e.hom ≫ (mappedIso p k n X U g a r).hom = (originalIso p k n X U g a r).hom :=
    comparison p k n X U g a r
  have hi := inv_prefix e _ _ he
  change ((AugmentedCech.CoefficientTotal.homologyIso (family p k n X U g a) (forget p k)
    ((single _ (.up ℕ) g).obj (coefficient p k n X U g)) (r+g)).hom ≫ e.inv) ≫ _ = _
  rw [Category.assoc, hi]
  exact coefficient_comparison p k n X U g a r

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopHomology
