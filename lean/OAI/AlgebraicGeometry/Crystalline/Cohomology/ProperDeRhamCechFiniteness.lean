import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperOrdinaryFormFiniteness
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiniteness
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Proper De Rham Cech Finiteness -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperDeRhamCechFiniteness.SmoothProperDeRhamCechFiniteness

noncomputable section

/-! # Finite cohomology of the original de Rham Cech total over any field -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))

def presheaves : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} k) ⥤
    X.left.Opensᵒᵖ ⥤ ModuleCat.{u} k :=
  sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} k)

instance presheaves_additive : (presheaves k X).Additive where
  map_add := rfl

def presheafComplex : CochainComplex (X.left.Opensᵒᵖ ⥤ ModuleCat.{u} k) ℕ :=
  ((presheaves k X).mapHomologicalComplex (.up ℕ)).obj (DeRhamGlobalId.DeRhamGlobal.sheafComplex k X)

variable [IsProper X.hom] [Smooth X.hom]

def bicomplex : HomologicalComplex₂ (ModuleCat.{u} k) (.up ℕ) (.up ℕ) :=
  NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total.bicomplex
    (FormalCoproduct.mk (NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleCover.Index k X)
      (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X)).cech (presheafComplex k X)

def total : CochainComplex (ModuleCat.{u} k) ℕ := (bicomplex k X).total (.up ℕ)

def rowIso (n : ℕ) :
    ProperCoherentCech.ProperCoherentCechFiniteness.complex k X (ProperOrdinaryFormFiniteness.SmoothProperOrdinaryFormFiniteness.term k X n)
      (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X) ≅ (bicomplex k X).X n :=
  (FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk (NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleCover.Index k X)
      (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X)).cech).mapIso
        ((presheaves k X).mapIso (OrdinaryFormSheaf.OrdinaryFormSheafComparison.iso k X n))

theorem row_finite (n q : ℕ) : Module.Finite k (((bicomplex k X).X n).homology q) := by
  let M := ProperOrdinaryFormFiniteness.SmoothProperOrdinaryFormFiniteness.term k X n
  let : M.IsQuasicoherent := ProperOrdinaryFormFiniteness.SmoothProperOrdinaryFormFiniteness.quasicoherent k X n
  let : M.IsFiniteType := ProperOrdinaryFormFiniteness.SmoothProperOrdinaryFormFiniteness.finiteType k X n
  let : Module.Finite k ((ProperCoherentCech.ProperCoherentCechFiniteness.complex k X M
      (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X)).homology q) :=
    ProperCoherentCech.ProperCoherentCechFiniteness.finite k X M (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X)
      (IsOpenCover.mk (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.cover k X))
      (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.affine k X) q
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (rowIso k X n) q).toLinearEquiv

theorem finite (n : ℕ) : Module.Finite k ((SmoothProperDeRhamCechFiniteness.total k X).homology n) :=
  NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiniteness.finite (bicomplex k X) n (fun q p _ => row_finite k X q p)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperDeRhamCechFiniteness.SmoothProperDeRhamCechFiniteness
