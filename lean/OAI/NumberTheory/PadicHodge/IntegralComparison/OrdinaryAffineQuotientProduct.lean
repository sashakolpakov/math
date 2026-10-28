import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryAffineTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BaseChangeTotalCup

/-! # Ordinary Affine Quotient Product -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.OrdinaryAffineQuotientProduct.Ordinary

/-! Literal affine-open coordinates of the original ordinary
coefficient-quotient Čech complex preserve its quotient wedge. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [X.left.IsSeparated]
  (I : Ideal R)

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left
local notation "A" => CategoryTheory.Functor.op F ⋙ OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.complex R I A
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.pairing R I A
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct.complex I (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
local notation "ν" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct.pairing I (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
  (IntegralDeRham.CechProduct.sectionPairing R X)

omit [X.left.IsSeparated] in
theorem component (i : ℕ) (V : X.left.affineOpensᵒᵖ)
    (x : ((P).X i).obj V) :
    ((GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.complexIso R X I).hom.f i).app V x = x := by
  obtain ⟨x, rfl⟩ := (I • ⊤ : Submodule R
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R Γ(X.left, V.unop.val) i)).mkQ_surjective x
  rfl

omit [X.left.IsSeparated] in
theorem component_pairing (i j : ℕ) (V : X.left.affineOpensᵒᵖ)
    (x : ((P).X i).obj V) (y : ((P).X j).obj V) :
    ((GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.complexIso R X I).hom.f (i+j)).app V (μ i j V x y) =
      Cech.BaseChangeTotalCup.Product.pairing F Q ν i j V
        (((GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.complexIso R X I).hom.f i).app V x)
        (((GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.complexIso R X I).hom.f j).app V y) := by
  rw [component, component, component]
  rfl

end NumberTheory.PadicHodge.IntegralComparison.OrdinaryAffineQuotientProduct.Ordinary

namespace NumberTheory.PadicHodge.IntegralComparison.OrdinaryAffineQuotientProduct.OrdinaryTotal

/-! The literal affine/open comparison used by the original finite
ordinary de Rham model preserves its actual total and cohomology cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

private theorem comp_pairing {R : Type*} [CommRing R]
    {K L M : CochainComplex (ModuleCat R) ℕ}
    (μ : ∀ i j, K.X i →ₗ[R] K.X j →ₗ[R] K.X (i+j))
    (ν : ∀ i j, L.X i →ₗ[R] L.X j →ₗ[R] L.X (i+j))
    (σ : ∀ i j, M.X i →ₗ[R] M.X j →ₗ[R] M.X (i+j))
    (a : K ⟶ L) (b : L ⟶ M) (c : K ⟶ M) (hc : c = a ≫ b)
    (ha : ∀ i j x y, a.f (i+j) (μ i j x y) = ν i j (a.f i x) (a.f j y))
    (hb : ∀ i j x y, b.f (i+j) (ν i j x y) = σ i j (b.f i x) (b.f j y))
    (i j : ℕ) (x : K.X i) (y : K.X j) :
    c.f (i+j) (μ i j x y) = σ i j (c.f i x) (c.f j y) := by
  subst c
  exact (congrArg (b.f (i+j)) (ha i j x y)).trans (hb i j _ _)

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [X.left.IsSeparated]
  {ι : Type} (U : ι → X.left.affineOpens) (I : Ideal R)

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left
local notation "A" => CategoryTheory.Functor.op F ⋙ OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.complex R I A
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.pairing R I A
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct.complex I (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
local notation "ν" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct.pairing I (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
  (IntegralDeRham.CechProduct.sectionPairing R X)
local notation "hν" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct.natural I (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
  (IntegralDeRham.CechProduct.sectionPairing R X)
  (IntegralDeRham.CechProduct.sectionPairing_natural R X)
local notation "dν" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct.differential I (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
  (IntegralDeRham.CechProduct.sectionPairing R X)
  (IntegralDeRham.CechProduct.sectionPairing_differential R X)
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "N'" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (Functor.obj F ∘ U)

local instance tuple_preserves (n : ℕ) (t : Fin (n+1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t)) F :=
  GeometricComparison.Affine.OpenProductPreservation.AffineOpenProductPreservation.inclusion_preserves X.left (U ∘ t)

theorem total_hom : (GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.totalIso R X U I).hom =
    Presheaf.CechProductNaturality.totalMap N (GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.complexIso R X I).hom ≫
      Cech.BaseChangeTotalCup.Product.map F U Q :=
  HomologicalComplex₂.total.map_comp _ _ (.up ℕ)

theorem map_cup (i j : ℕ) (x : (Presheaf.TotalCup.CechProduct.total N P).X i) (y : (Presheaf.TotalCup.CechProduct.total N P).X j) :
    ((GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.totalIso R X U I).hom.f (i+j)) (Presheaf.TotalCup.CechProduct.totalCup N P μ i j x y) =
      Presheaf.TotalCup.CechProduct.totalCup N' Q ν i j
        (((GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.totalIso R X U I).hom.f i) x)
        (((GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.totalIso R X U I).hom.f j) y) :=
  comp_pairing (Presheaf.TotalCup.CechProduct.totalCup N P μ)
    (Presheaf.TotalCup.CechProduct.totalCup N (Cech.BaseChangeTotalCup.Product.pulled F Q)
      (Cech.BaseChangeTotalCup.Product.pairing F Q ν))
    (Presheaf.TotalCup.CechProduct.totalCup N' Q ν) _ _ _ (total_hom R X U I)
    (Presheaf.CechProductNaturality.totalMap_pairing N μ (Cech.BaseChangeTotalCup.Product.pairing F Q ν)
      (GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.complexIso R X I).hom
      (Ordinary.component_pairing R X I))
    (Cech.BaseChangeTotalCup.Product.map_cup F U Q ν hν) i j x y

abbrev cohomologyMap_cup := Cochain.CupNaturality.Cohomology.cohomologyMap_cup
  (Presheaf.TotalCup.CechProduct.totalCup N P μ) (Presheaf.TotalCup.CechProduct.totalCup N' Q ν)
  (Presheaf.TotalLeibniz.CechProduct.differential_totalCup N P μ (OrdinaryQuotientDiagramProduct.Ordinary.natural R I A)
    (OrdinaryQuotientDiagramProduct.Ordinary.differential R I A))
  (Presheaf.TotalLeibniz.CechProduct.differential_totalCup N' Q ν hν dν)
  (GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.totalIso R X U I).hom (map_cup R X U I)

end NumberTheory.PadicHodge.IntegralComparison.OrdinaryAffineQuotientProduct.OrdinaryTotal

end

end OAI
