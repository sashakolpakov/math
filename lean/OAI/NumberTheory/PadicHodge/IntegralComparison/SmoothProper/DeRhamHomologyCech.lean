import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamHomologyUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.HomologyCechFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamCechUnit

/-! # De Rham Homology Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamHomologyCech

noncomputable section

/-! Original de Rham homology presheaves have finite Cech cohomology on the actual finite cover. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Simplicial _root_.TopologicalSpace

universe u

variable (k : Type u) [Field k] [Fintype k]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamCechUnit OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.HomologyPresheaf

def complex (n : ℕ) : CochainComplex (ModuleCat.{u} k) ℕ :=
  (FormalCoproduct.cochainComplexFunctor (DeRhamCechUnit.nerve k X)).obj ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k X).homology n)

def target (n : ℕ) : CochainComplex (ModuleCat.{u} k) ℕ :=
  (FormalCoproduct.cochainComplexFunctor (DeRhamCechUnit.nerve k X)).obj (Frobenius.HomologyPresheaf.sheafHomology k X n)

def map (n : ℕ) : complex k X n ⟶ target k X n :=
  (FormalCoproduct.cochainComplexFunctor (DeRhamCechUnit.nerve k X)).map (Frobenius.HomologyPresheaf.rawHomologyMap k X n)

theorem component_isIso (n q : ℕ) : IsIso ((DeRhamHomologyCech.map k X n).f q) := by
  let E := (DeRhamCechUnit.nerve k X).obj (op ⦋q⦌)
  change IsIso (Limits.Pi.map (fun i : E.I => (Frobenius.HomologyPresheaf.rawHomologyMap k X n).app (op (E.obj i))))
  have (i : E.I) : IsIso ((Frobenius.HomologyPresheaf.rawHomologyMap k X n).app (op (E.obj i))) :=
    DeRhamHomologyUnit.chart_rawHomologyMap_isIso k X q i n
  infer_instance

theorem map_isIso (n : ℕ) : IsIso (DeRhamHomologyCech.map k X n) := by
  have (q : ℕ) : IsIso ((DeRhamHomologyCech.map k X n).f q) := component_isIso k X n q
  exact HomologicalComplex.Hom.isIso_of_components _

def iso (n : ℕ) : complex k X n ≅ target k X n := by
  have := map_isIso k X n
  exact asIso (DeRhamHomologyCech.map k X n)

theorem target_finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n q : ℕ) :
    Module.Finite k ((target k X n).homology q) := by
  let : (FrobeniusHomology.cohomology k X n).IsQuasicoherent :=
    FrobeniusHomology.quasicoherent k X n
  let : (FrobeniusHomology.cohomology k X n).IsFiniteType :=
    FrobeniusHomology.finiteType k X n
  exact Projective.HomologyCechFiniteness.finite k X
    (FrobeniusHomology.cohomology k X n) (FrobeniusCharts.opens k X)
    hprojective (IsOpenCover.mk (FrobeniusCharts.cover k X))
    (FrobeniusCharts.affine k X) q

theorem finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n q : ℕ) :
    Module.Finite k ((complex k X n).homology q) := by
  let : Module.Finite k ((target k X n).homology q) := target_finite k X hprojective n q
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (iso k X n) q).symm.toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamHomologyCech
