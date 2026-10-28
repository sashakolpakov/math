import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.HomologyPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.HomologyIsIso

/-! # De Rham Homology Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamHomologyUnit

noncomputable section

/-! The canonical original de Rham homology comparison is invertible on every actual Cech intersection. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable (k : Type u) [Field k] [Fintype k]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (q : ℕ) (t : Fin (q + 1) → EtaleCover.Index k X)

open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechIntersections OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.HomologyPresheaf

theorem evaluated_rawMap_isIso : IsIso
    ((DeRhamSheafificationUnit.evaluation k X (CechIntersections.opens k X q t)).map (Frobenius.HomologyPresheaf.rawMap k X)) := by
  let F := DeRhamSheafificationUnit.evaluation k X (CechIntersections.opens k X q t)
  have : IsIso (F.map (DeRhamSheafificationUnit.map k X)) :=
    DeRhamUnit.evaluated_isIso k X q t
  change IsIso (F.map (DeRhamSheafificationUnit.map k X ≫ (Frobenius.HomologyPresheaf.underlyingIso k X).inv))
  rw [F.map_comp]
  infer_instance

theorem rawHomologyMap_isIso (n : ℕ) :
    IsIso ((Frobenius.HomologyPresheaf.rawHomologyMap k X n).app (op (CechIntersections.opens k X q t))) := by
  let G := (CategoryTheory.evaluation X.left.Opensᵒᵖ (ModuleCat.{u} k)).obj (op (CechIntersections.opens k X q t))
  have : IsIso ((G.mapHomologicalComplex (.up ℕ)).map (Frobenius.HomologyPresheaf.rawMap k X)) := evaluated_rawMap_isIso k X q t
  have : IsIso ((HomologicalComplex.homologyMap (Frobenius.HomologyPresheaf.rawMap k X) n).app (op (CechIntersections.opens k X q t))) :=
    Mapped.HomologyIsIso.of_quasiIsoAt G (Frobenius.HomologyPresheaf.rawMap k X) n
  have : IsIso ((Frobenius.HomologyPresheaf.comparison k X n).app (op (CechIntersections.opens k X q t))) :=
    Frobenius.HomologyPresheaf.affine_comparison_isIso k X (CechIntersections.opens k X q t) (CechIntersections.affine k X q t) n
  change IsIso ((HomologicalComplex.homologyMap (Frobenius.HomologyPresheaf.rawMap k X) n).app (op (CechIntersections.opens k X q t)) ≫
    (Frobenius.HomologyPresheaf.comparison k X n).app (op (CechIntersections.opens k X q t)))
  infer_instance

theorem chart_rawHomologyMap_isIso (n : ℕ) :
    IsIso ((Frobenius.HomologyPresheaf.rawHomologyMap k X n).app
      (op (∏ᶜ fun j : Fin (q + 1) => FrobeniusCharts.opens k X (t j)))) := by
  exact (congrArg (fun U : X.left.Opens => IsIso ((Frobenius.HomologyPresheaf.rawHomologyMap k X n).app (op U)))
    (DeRhamUnit.chart_intersection k X q t)).mpr (rawHomologyMap_isIso k X q t n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamHomologyUnit
