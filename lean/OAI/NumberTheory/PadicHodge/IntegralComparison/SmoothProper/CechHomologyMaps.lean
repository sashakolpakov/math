import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechDeRhamNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologyLocal

/-! # Cech Homology Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechHomologyMaps

noncomputable section

/-! The actual local comparisons define compatible maps on the original homology presheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechIntersections

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0)) (i : ℕ)

local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Global.DeRhamCoefficientComplex.complex p k X
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.complex (OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X) 0 I

def map (q : ℕ) (t : Fin (q + 1) → EtaleCover.Index k X) :
    ((D).homology i).obj (op (CechIntersections.opens k X q t)) ⟶ ((L).homology i).obj (op (CechIntersections.opens k X q t)) :=
  Functor.HomologyLocal.Comparison.map D L i (op (CechIntersections.opens k X q t)) (CechDeRham.map p k X I q t)

instance map_isIso (q : ℕ) (t : Fin (q + 1) → EtaleCover.Index k X) :
    IsIso (CechHomologyMaps.map p k X I i q t) :=
  ((Functor.HomologyEvaluation.component D i (op (CechIntersections.opens k X q t))).symm ≪≫
    CechDeRham.homologyIso p k X I q t i ≪≫
      Functor.HomologyEvaluation.component L i (op (CechIntersections.opens k X q t))).isIso_hom

theorem naturality (m n : ℕ) (s : Fin (m + 1) → EtaleCover.Index k X)
    (t : Fin (n + 1) → EtaleCover.Index k X) (h : CechIntersections.opens k X n t ≤ CechIntersections.opens k X m s) :
    ((D).homology i).map (homOfLE h).op ≫ CechHomologyMaps.map p k X I i n t =
      CechHomologyMaps.map p k X I i m s ≫ ((L).homology i).map (homOfLE h).op :=
  Functor.HomologyLocal.Comparison.naturality D L i (homOfLE h).op
    (CechDeRham.map p k X I m s) (CechDeRham.map p k X I n t)
    (CechDeRhamNaturality.homology p k X I m n s t h i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechHomologyMaps
