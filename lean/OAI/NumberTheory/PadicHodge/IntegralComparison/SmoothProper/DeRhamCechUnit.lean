import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamFiniteness

/-! # De Rham Cech Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamCechUnit

noncomputable section

/-! The actual raw de Rham Čech total maps isomorphically to the original sheaf Čech total. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u

variable (k : Type u) [Field k] [Fintype k]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

abbrev nerve := (FormalCoproduct.mk (EtaleCover.Index k X)
  (FrobeniusCharts.opens k X)).cech

def bicomplex : HomologicalComplex₂ (ModuleCat.{u} k) (.up ℕ) (.up ℕ) :=
  CechCoefficient.Total.bicomplex (nerve k X) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k X)

def map : bicomplex k X ⟶ DeRhamCechTotal.bicomplex k X (FrobeniusCharts.opens k X) :=
  ((FormalCoproduct.cochainComplexFunctor (nerve k X)).mapHomologicalComplex (.up ℕ)).map
    (DeRhamSheafificationUnit.map k X)

theorem component_isIso (n q : ℕ) : IsIso (((DeRhamCechUnit.map k X).f n).f q) := by
  let E := (nerve k X).obj (op ⦋q⦌)
  change IsIso (Limits.Pi.map (fun i : E.I =>
    (toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k X n)).app (op (E.obj i))))
  have (i : E.I) : IsIso ((toSheafify (Opens.grothendieckTopology X.left)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k X n)).app (op (E.obj i))) :=
    DeRhamUnit.chart_forms k X q i n
  infer_instance

theorem map_isIso : IsIso (DeRhamCechUnit.map k X) := by
  have (n q : ℕ) : IsIso (((DeRhamCechUnit.map k X).f n).f q) := component_isIso k X n q
  have (n : ℕ) : IsIso ((DeRhamCechUnit.map k X).f n) := HomologicalComplex.Hom.isIso_of_components _
  exact HomologicalComplex.Hom.isIso_of_components _

def total : CochainComplex (ModuleCat.{u} k) ℕ := (bicomplex k X).total (.up ℕ)

def totalMap : DeRhamCechUnit.total k X ⟶ DeRhamFiniteness.total k X :=
  HomologicalComplex₂.total.map (DeRhamCechUnit.map k X) (.up ℕ)

theorem totalMap_isIso : IsIso (totalMap k X) := by
  let : IsIso (DeRhamCechUnit.map k X) := map_isIso k X
  exact (HomologicalComplex₂.total.mapIso (asIso (DeRhamCechUnit.map k X)) (.up ℕ)).isIso_hom

def totalIso : DeRhamCechUnit.total k X ≅ DeRhamFiniteness.total k X := by
  let : IsIso (totalMap k X) := totalMap_isIso k X
  exact asIso (totalMap k X)

theorem finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n : ℕ) :
    Module.Finite k ((DeRhamCechUnit.total k X).homology n) := by
  let : Module.Finite k ((DeRhamFiniteness.total k X).homology n) :=
    DeRhamFiniteness.finite k X hprojective n
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (totalIso k X) n).symm.toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamCechUnit
