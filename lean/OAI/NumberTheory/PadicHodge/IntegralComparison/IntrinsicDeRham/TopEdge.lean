import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.FormDegreeBound
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.FormCoherence
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.DimensionBound
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdgeSurjective
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdgeNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Top Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdge.Intrinsic

noncomputable section

/-! The actual top-form Čech cohomology maps onto the native de Rham
Čech total in degree twice the relative dimension. No degeneration
of the integral Hodge-to-de Rham sequence is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex.Intrinsic

universe u

variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R)))
  {ι : Type u} (U : ι → X.left.Opens)

def rowIso (n : ℕ) :
    ModuleCech.DimensionBound.complex R X (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n) U ≅
      (CechComplex.Intrinsic.bicomplex R X U).X n :=
  (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).mapIso
    ((CechComplex.Intrinsic.presheaves R X).mapIso (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X n))

variable (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]

include g in
theorem row_isZero (n : ℕ) (hn : g < n) : IsZero ((CechComplex.Intrinsic.bicomplex R X U).X n) :=
  (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).map_isZero
    ((CechComplex.Intrinsic.presheaves R X).map_isZero (IntegralComparison.Smooth.FormDegreeBound.coefficient_sheaf_isZero R X g n hn))

theorem term_isZero (a b : ℕ) (ha : g < a) : IsZero (((CechComplex.Intrinsic.bicomplex R X U).X a).X b) :=
  (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) b).map_isZero (row_isZero R X U g a ha)

theorem outgoing (q : ℕ) : ((CechComplex.Intrinsic.bicomplex R X U).d g (g + 1)).f q = 0 :=
  (term_isZero R X U g (g + 1) q (Nat.lt_succ_self g)).eq_of_tgt _ _

abbrev source : ModuleCat.{u} R :=
  (ModuleCech.DimensionBound.complex R X (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g) U).homology g

def map : source R X U g →ₗ[R] (CechComplex.Intrinsic.total R X U).homology (g + g) :=
  (TopRowEdge.map (CechComplex.Intrinsic.bicomplex R X U) g (outgoing R X U g) g).comp
    (HomologicalComplex.homologyMap (rowIso R X U g).hom g).hom

theorem surjective [NoetherianSpace X.left]
    (hU : ⨆ i, U i = ⊤) (haffine : ∀ i, IsAffineOpen (U i))
    (hdim : topologicalKrullDim X.left ≤ (g : WithBot ℕ∞)) :
    Function.Surjective (map R X U g) := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  let : X.left.IsSeparated := ⟨by
    have h : IsSeparated (X.hom ≫ terminal.from _) := inferInstance
    simpa only [terminal.comp_from] using h⟩
  have hs : Function.Surjective (TopRowEdge.map (CechComplex.Intrinsic.bicomplex R X U) g (outgoing R X U g) g) := by
    apply TopRowEdgeSurjective.surjective (CechComplex.Intrinsic.bicomplex R X U) g (outgoing R X U g)
      (fun a b ha => ModuleCat.subsingleton_of_isZero (term_isZero R X U g a b ha)) g
    intro q hq
    let : (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X q).IsQuasicoherent :=
      IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R X q
    let := ModuleCech.DimensionBound.vanishing R X
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X q) U hU haffine g hdim (g + g - q) (by omega)
    exact (HomologicalComplex.homologyMapIso (rowIso R X U q) (g + g - q)).symm.toLinearEquiv.injective.subsingleton
  exact hs.comp (ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap (rowIso R X U g).hom g)).surjective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdge.Intrinsic
