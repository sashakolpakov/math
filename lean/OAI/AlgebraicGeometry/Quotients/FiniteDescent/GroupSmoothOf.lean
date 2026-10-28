import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeFiniteness
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Group Smooth Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupSmoothOf.Construction.GroupSmooth

/-!
# Smoothness of finite locally free group-scheme quotients

Flatness and finite presentation descend through the quotient. Its geometric
fibers are reduced group schemes, hence smooth; the smooth-fiber criterion
then establishes smoothness over the original base.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- A flat group scheme locally of finite presentation with geometrically
reduced fibers is smooth. -/
theorem smooth_of_flat_geometricallyReduced
    {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [Flat G.hom] [LocallyOfFinitePresentation G.hom] [GeometricallyReduced G.hom] :
    Smooth G.hom := by
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro s
  let : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  let : GrpObj (Over.mk (G.hom.fiberToSpecResidueField s)) := Over.grpObjMkPullbackSnd
  have hft : LocallyOfFiniteType (G.hom.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd G.hom (S.fromSpecResidueField s)))
  exact @smooth_of_grpObj _ _ _ (G.hom.fiberToSpecResidueField s) hft
    (inferInstanceAs (GrpObj (Over.mk (G.hom.fiberToSpecResidueField s))))
    (inferInstanceAs (GeometricallyReduced (G.hom.fiberToSpecResidueField s)))

/-- A finite locally free quotient of a smooth group scheme is smooth over
the original base. -/
theorem smooth_of_finite_quotient
    {S : Scheme.{u}} {A B : Over S} [GrpObj B] [Smooth A.hom]
    (q : A ⟶ B) [IsFinite q.left] [Flat q.left] [Surjective q.left]
    [LocallyOfFinitePresentation q.left] : Smooth B.hom := by
  have : Smooth (q.left ≫ B.hom) := by rw [q.w]; infer_instance
  have : GeometricallyReduced (q.left ≫ B.hom) :=
    SchemeSmooth.Construction.SchemeSmoothReduced.geometricallyReduced_of_smooth _
  have : GeometricallyReduced B.hom := SchemeSmooth.Construction.SchemeSmoothReduced.geometricallyReduced_of_comp q.left B.hom
  have : Flat B.hom := SchemeFiniteness.Construction.SchemeFinitenessDescent.flat q.left B.hom
  have : LocallyOfFinitePresentation B.hom :=
    SchemeFiniteness.Construction.SchemeFinitenessDescent.locallyOfFinitePresentation q.left B.hom
  exact smooth_of_flat_geometricallyReduced B

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupSmoothOf.Construction.GroupSmooth
