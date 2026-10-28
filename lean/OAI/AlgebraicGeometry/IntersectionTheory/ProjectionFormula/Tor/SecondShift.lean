import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionAugment
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Flat

/-! # Second Shift -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.SecondShift

noncomputable section

/-! Positive-degree dimension shifting in the second variable of native
Tor, computed from the explicitly augmented projective resolution. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

universe u

variable (R : Type u) [CommRing R] (N : ModuleCat.{u} R)
  (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact) [Projective S.X₂]

def shiftIso (n : ℕ) : (((Tor (ModuleCat R) (n + 2)).obj N).obj S.X₃) ≅
    (((Tor (ModuleCat R) (n + 1)).obj N).obj S.X₁) := by
  let Q := projectiveResolution S.X₁
  let P := ResolutionAugment.resolution S hS Q
  let F := (tensorLeft N).mapHomologicalComplex (ComplexShape.down ℕ)
  let e : (F.obj P.complex).sc' (n + 3) (n + 2) (n + 1) ≅
      (F.obj Q.complex).sc' (n + 2) (n + 1) n :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [F, P, ResolutionAugment.resolution, ResolutionAugment.complex])
      (by simp [F, P, ResolutionAugment.resolution, ResolutionAugment.complex])
  exact P.isoLeftDerivedObj (tensorLeft N) (n + 2) ≪≫
    (F.obj P.complex).homologyIsoSc' (n + 3) (n + 2) (n + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso e ≪≫
    ((F.obj Q.complex).homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).symm ≪≫
    (Q.isoLeftDerivedObj (tensorLeft N) (n + 1)).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.SecondShift
