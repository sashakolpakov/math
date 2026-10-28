import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormFiniteness
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiniteness
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Proper De Rham Cech Finiteness -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperDeRhamCechFiniteness.BaseSmoothProperDeRhamCechFiniteness

noncomputable section

/-! # Finite cohomology of the original de Rham Cech total over a noetherian commutative base -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (k : Type u) [CommRing k] (X : Over (Spec (CommRingCat.of k)))

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
    (FormalCoproduct.mk (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index k X)
      (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens k X)).cech (presheafComplex k X)

def total : CochainComplex (ModuleCat.{u} k) ℕ := (bicomplex k X).total (.up ℕ)

def rowIso (n : ℕ) :
    ProperCoherentCech.ProperCoherentCechFiniteness.complex k X (ProperOrdinaryFormFiniteness.BaseSmoothProperOrdinaryFormFiniteness.term k X n)
      (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens k X) ≅ (bicomplex k X).X n :=
  (FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index k X)
      (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens k X)).cech).mapIso
        ((presheaves k X).mapIso (OrdinaryFormSheaf.OrdinaryFormSheafComparison.iso k X n))

variable [IsNoetherianRing k]

theorem row_finite (n q : ℕ) : Module.Finite k (((bicomplex k X).X n).homology q) := by
  let M := ProperOrdinaryFormFiniteness.BaseSmoothProperOrdinaryFormFiniteness.term k X n
  let : M.IsQuasicoherent := ProperOrdinaryFormFiniteness.BaseSmoothProperOrdinaryFormFiniteness.quasicoherent k X n
  let : M.IsFiniteType := ProperOrdinaryFormFiniteness.BaseSmoothProperOrdinaryFormFiniteness.finiteType k X n
  let : Module.Finite k ((ProperCoherentCech.ProperCoherentCechFiniteness.complex k X M
      (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens k X)).homology q) :=
    ProperCoherentCech.ProperCoherentCechFiniteness.finite k X M (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens k X)
      (IsOpenCover.mk (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.cover k X))
      (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.affine k X) q
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (rowIso k X n) q).toLinearEquiv

theorem finite (n : ℕ) : Module.Finite k ((BaseSmoothProperDeRhamCechFiniteness.total k X).homology n) :=
  NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiniteness.finite (bicomplex k X) n (fun q p _ => row_finite k X q p)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperDeRhamCechFiniteness.BaseSmoothProperDeRhamCechFiniteness
