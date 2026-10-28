import OAI.AlgebraicGeometry.CycleClass.Geometric.FrontierClosedFiltration
import OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedSupportFiltration
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.StratificationPointPartition
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.StratumDimensionBounds
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SupportRegularBoundary

/-! # Analytic Support Filtration -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.AnalyticSupportFiltration

noncomputable section

/-!
# Closed analytic filtrations of genuine algebraic supports

The previously constructed finite algebraic stratification has an ordered
frontier condition. Its actual analytic supports therefore give an increasing
closed filtration. Each layer is exactly the analytic image of one of the
original integral smooth pieces. Applied to a singular boundary, its layers
have complex codimension at least one more than the original support.

No cohomological purity premise is included in these geometric constructions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Set

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}

theorem listSupport_map_analyticSupport
    (Ps : List (IntegralSmoothStratification.IntegralSmoothGeometricPiece f)) :
    FrontierClosedFiltration.Cycles.listSupport (Ps.map fun P => P.analyticSupport) =
      ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport Ps := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih =>
      simp only [List.map_cons, FrontierClosedFiltration.Cycles.listSupport_cons,
        ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport, ih]

theorem listFrontier_map_analyticSupport
    (Ps : List (IntegralSmoothStratification.IntegralSmoothGeometricPiece f))
    (h : ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticFrontier Ps) :
    FrontierClosedFiltration.Cycles.listFrontier (Ps.map fun P => P.analyticSupport) := by
  induction Ps with
  | nil => trivial
  | cons P Ps ih =>
      change (closure P.analyticSupport \ P.analyticSupport ⊆
        FrontierClosedFiltration.Cycles.listSupport (Ps.map fun Q => Q.analyticSupport)) ∧ _
      rw [listSupport_map_analyticSupport]
      exact ⟨h.1, ih h.2⟩

namespace IntegralSmoothGeometricStratification

variable {S : Set X} (Q : IntegralSmoothStratification.IntegralSmoothGeometricStratification f S)

/-- The unchanged list of actual analytic supports. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticSupportList : List (Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f))) :=
  Q.pieces.map fun P => P.analyticSupport

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticSupportList_frontier : FrontierClosedFiltration.Cycles.listFrontier Q.analyticSupportList :=
  listFrontier_map_analyticSupport Q.pieces Q.analyticSupport_frontier

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticSupportList_pairwise : Q.analyticSupportList.Pairwise Disjoint := by
  simpa only [IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticSupportList, List.pairwise_map] using
    Q.pairwise_disjoint_analyticSupport

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticSupportList_support :
    FrontierClosedFiltration.Cycles.listSupport Q.analyticSupportList = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' S := by
  rw [IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticSupportList, listSupport_map_analyticSupport, Q.analyticSupport_cover]

/-- An actual increasing finite filtration by closed analytic subsets. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticClosedFiltration :
    Fin (Q.analyticSupportList.length + 1) →
      Closeds (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)) :=
  FrontierClosedFiltration.Cycles.frontierClosedFiltration Q.analyticSupportList Q.analyticSupportList_frontier

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticClosedFiltration_monotone : Monotone Q.analyticClosedFiltration :=
  FrontierClosedFiltration.Cycles.frontierClosedFiltration_monotone _ _

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticClosedFiltration_zero : Q.analyticClosedFiltration 0 = ⊥ :=
  FrontierClosedFiltration.Cycles.frontierClosedFiltration_zero _ _

/-- The filtration covers precisely the original support's analytic points. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticClosedFiltration_last :
    (Q.analyticClosedFiltration (Fin.last Q.analyticSupportList.length) :
      Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f))) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' S :=
  (FrontierClosedFiltration.Cycles.frontierClosedFiltration_last Q.analyticSupportList
    Q.analyticSupportList_frontier).trans Q.analyticSupportList_support

/-- The original smooth piece occurring in one layer of the reversed filtration. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationPiece (i : Fin Q.analyticSupportList.length) :
    IntegralSmoothStratification.IntegralSmoothGeometricPiece f :=
  Q.pieces.get ⟨i.rev.val, by simpa only [IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticSupportList, List.length_map] using i.rev.isLt⟩

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationPiece_mem (i : Fin Q.analyticSupportList.length) :
    Q.analyticFiltrationPiece i ∈ Q.pieces := List.get_mem _ _

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationPiece_support (i : Fin Q.analyticSupportList.length) :
    (Q.analyticFiltrationPiece i).analyticSupport = Q.analyticSupportList.get i.rev := by
  simp only [IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationPiece, IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticSupportList, List.get_eq_getElem,
    List.getElem_map]

/-- Every layer is the image of its actual integral smooth scheme piece. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticClosedFiltration_layer (i : Fin Q.analyticSupportList.length) :
    (Q.analyticClosedFiltration i.succ : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f))) \
        Q.analyticClosedFiltration i.castSucc =
      (Q.analyticFiltrationPiece i).analyticSupport := by
  exact (FrontierClosedFiltration.Cycles.frontierClosedFiltration_layer Q.analyticSupportList
    Q.analyticSupportList_frontier Q.analyticSupportList_pairwise i).trans
      (Q.analyticFiltrationPiece_support i).symm

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticClosedFiltration_layer_eq_range (i : Fin Q.analyticSupportList.length) :
    (Q.analyticClosedFiltration i.succ : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f))) \
        Q.analyticClosedFiltration i.castSucc =
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Q.analyticFiltrationPiece i).toAmbient) := by
  rw [Q.analyticClosedFiltration_layer,
    (Q.analyticFiltrationPiece i).analyticSupport_eq_range]

/-- Inside the complement of the previous closed stage, the next layer is
the same genuine analytic smooth piece, with the subspace topology. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticClosedFiltration_relativeLayer_image
    (i : Fin Q.analyticSupportList.length) :
    Subtype.val '' ClosedSupportFiltration.Cycles.closedSupportLayer
        (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)))
        (Q.analyticClosedFiltration i.castSucc) (Q.analyticClosedFiltration i.succ) =
      (Q.analyticFiltrationPiece i).analyticSupport := by
  rw [ClosedSupportFiltration.Cycles.closedSupportLayer_image, Q.analyticClosedFiltration_layer]

end IntegralSmoothGeometricStratification

namespace DimensionCycleSupport

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

private theorem ambient_noetherianSpace (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    NoetherianSpace V.carrier := by
  let : IsLocallyNoetherian V.carrier :=
    LocallyOfFiniteType.isLocallyNoetherian V.structureMap
  let : CompactSpace V.carrier := (quasiCompact_iff_compactSpace V.structureMap).mp
    (inferInstance : QuasiCompact V.structureMap)
  let : IsNoetherian V.carrier := ⟨⟩
  infer_instance

/-- A finite stratification of the actual singular boundary, chosen only
after its existence has been proved by Noetherian induction. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryStratification (Z : DimensionCycles.DimensionCycleSupport V p) :
    IntegralSmoothStratification.IntegralSmoothGeometricStratification V.structureMap
      (StratumDimension.supportSingularBoundary Z.1 V.structureMap) := by
  let : NoetherianSpace V.carrier := ambient_noetherianSpace V
  exact Classical.choice (IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_closed
    V.structureMap ⟨StratumDimension.supportSingularBoundary Z.1 V.structureMap,
      StratumDimension.isClosed_supportSingularBoundary Z.1 V.structureMap⟩)

/-- The singular boundary's canonical chosen finite closed analytic filtration. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryClosedFiltration (Z : DimensionCycles.DimensionCycleSupport V p) :=
  Z.singularBoundaryStratification.analyticClosedFiltration

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryClosedFiltration_last (Z : DimensionCycles.DimensionCycleSupport V p) :
    (Z.singularBoundaryClosedFiltration
      (Fin.last Z.singularBoundaryStratification.analyticSupportList.length) :
        Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap))) = Z.analyticSingularBoundary :=
  Z.singularBoundaryStratification.analyticClosedFiltration_last

/-- Each layer's actual complex manifold has dimension strictly less than
the original support dimension. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryClosedFiltration_piece_dimension
    (Z : DimensionCycles.DimensionCycleSupport V p)
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length) :
    (Z.singularBoundaryStratification.analyticFiltrationPiece i).complexDimension <
      V.complexDimension - p :=
  Z.singularBoundaryStratum_complexDimension_lt_sub _
    (Z.singularBoundaryStratification.piece_support_subset
      (Z.singularBoundaryStratification.analyticFiltrationPiece_mem i))

/-- The layer has at least the codimension required to kill both obstruction
degrees for extension of a codimension-p class. This is a dimension statement,
not an assumption of cohomological purity. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryClosedFiltration_piece_codimension
    (Z : DimensionCycles.DimensionCycleSupport V p)
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length) :
    (Z.singularBoundaryStratification.analyticFiltrationPiece i).complexDimension +
      p + 1 ≤ V.complexDimension := by
  have h := Z.singularBoundaryClosedFiltration_piece_dimension i
  omega

end DimensionCycleSupport

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.AnalyticSupportFiltration
