import OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification
import OAI.AlgebraicGeometry.Foundations.Scheme.ComplexPointExistence
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointUnderlying
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.CycleStratumRealization
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeImmersionPointTopology
import Mathlib.Topology.LocallyClosed

/-! # Stratification Point Partition -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# The actual analytic point partition of an integral smooth stratification

Every support is the inverse image of the actual scheme support under the
underlying-point map. The finite list and its order are unchanged. Continuity
transports local closedness and the closure-minus-piece containment in later
pieces; no equality of Zariski and analytic closures is asserted.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}

section

/-- The ordinary analytic points lying in the actual scheme support. -/
def CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSupport (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)) :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' P.support

@[simp]
theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.mem_analyticSupport (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)) :
    x ∈ P.analyticSupport ↔ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ P.support := Iff.rfl

theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.isLocallyClosed_analyticSupport (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    IsLocallyClosed P.analyticSupport :=
  P.isLocallyClosed_support.preimage ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_underlying

/-- Every integral smooth piece has actual complex points in its analytic support. -/
theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSupport_nonempty (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.analyticSupport.Nonempty := by
  obtain ⟨x⟩ := Foundations.Scheme.ComplexPointExistence.nonempty_complexOverPoints (P.inclusion ≫ f)
  refine ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
    (Over.homMk P.inclusion rfl : Over.mk (P.inclusion ≫ f) ⟶ Over.mk f) x, ?_⟩
  exact ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x, rfl⟩

/-- Analytic closure maps into scheme closure, with their respective topologies. -/
theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.closure_analyticSupport_subset (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    closure P.analyticSupport ⊆ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' closure P.support :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_underlying (X := Over.mk f)).closure_preimage_subset P.support

/-- The closure-minus-piece containment needed for the ordered stratification. -/
theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.closure_sdiff_analyticSupport_subset (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    closure P.analyticSupport \ P.analyticSupport ⊆
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (closure P.support \ P.support) := by
  intro x hx
  exact ⟨P.closure_analyticSupport_subset hx.1, hx.2⟩

theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.disjoint_analyticSupport_of_disjoint (P Q : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f)
    (h : Disjoint P.support Q.support) : Disjoint P.analyticSupport Q.analyticSupport := by
  apply Set.disjoint_left.mpr
  intro x hxP hxQ
  exact Set.disjoint_left.mp h hxP hxQ

/-- The support is exactly the image of the native point map of this actual piece. -/
theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSupport_eq_range (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.analyticSupport = Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.toAmbient) := by
  let : IsImmersion P.toAmbient.left := P.immersion
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion P.toAmbient).symm

/-- The native analytic space of the piece carries precisely the support's subspace topology. -/
def CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSupportHomeomorph (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.analyticSpace ≃ₜ P.analyticSupport := by
  let : IsImmersion P.toAmbient.left := P.immersion
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion P.toAmbient).toHomeomorph.trans
    (Homeomorph.setCongr P.analyticSupport_eq_range.symm)

@[simp]
theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticSupportHomeomorph_val (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f)
    (x : P.analyticSpace) :
    (P.analyticSupportHomeomorph x).val = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.toAmbient x := rfl

end

/-- The analytic support of the unchanged finite list of geometric pieces. -/
def ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport :
    List (CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) → Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f))
  | [] => ∅
  | P :: Ps => P.analyticSupport ∪ integralSmoothPiecesAnalyticSupport Ps

theorem ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport_eq_preimage
    (Ps : List (CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f)) :
    ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport Ps =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' CycleClass.Geometric.IntegralSmoothStratification.integralSmoothPiecesSupport Ps := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih =>
      change P.analyticSupport ∪ ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport Ps =
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (P.support ∪ CycleClass.Geometric.IntegralSmoothStratification.integralSmoothPiecesSupport Ps)
      rw [Set.preimage_union, ih]
      rfl

theorem ComplexPoints.Analytic.StratificationPointPartition.mem_integralSmoothPiecesAnalyticSupport
    (Ps : List (CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f)) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)) :
    x ∈ ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport Ps ↔
      ∃ P ∈ Ps, x ∈ P.analyticSupport := by
  induction Ps with
  | nil => simp [ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport]
  | cons P Ps ih => simp [ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport, ih]

theorem ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport_eq_biUnion
    (Ps : List (CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f)) :
    ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport Ps = ⋃ P ∈ Ps, P.analyticSupport := by
  ext x
  simp only [ComplexPoints.Analytic.StratificationPointPartition.mem_integralSmoothPiecesAnalyticSupport, Set.mem_iUnion, exists_prop]

/-- The exact closure-minus-piece condition, in the original order of the list. -/
def ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticFrontier : List (CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) → Prop
  | [] => True
  | P :: Ps => closure P.analyticSupport \ P.analyticSupport ⊆
      ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport Ps ∧ integralSmoothPiecesAnalyticFrontier Ps

theorem ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesFrontier_analytic
    (Ps : List (CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f)) (h : CycleClass.Geometric.IntegralSmoothStratification.integralSmoothPiecesFrontier Ps) :
    ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticFrontier Ps := by
  induction Ps with
  | nil => trivial
  | cons P Ps ih =>
      refine ⟨?_, ih h.2⟩
      rw [ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport_eq_preimage]
      intro x hx
      exact h.1 (P.closure_sdiff_analyticSupport_subset hx)

section

variable {S : Set X} (Q : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification f S)

/-- Pullback preserves the proved pairwise disjointness of the actual pieces. -/
theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.pairwise_disjoint_analyticSupport :
    Q.pieces.Pairwise (fun P R => Disjoint P.analyticSupport R.analyticSupport) := by
  apply Q.disjoint.imp
  intro P R h
  exact P.disjoint_analyticSupport_of_disjoint R h

/-- The ordinary analytic pieces cover exactly the intended scheme support's points. -/
theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticSupport_cover :
    ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport Q.pieces =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' S := by
  rw [ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport_eq_preimage, Q.cover]

theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticSupport_biUnion :
    (⋃ P ∈ Q.pieces, P.analyticSupport) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' S := by
  rw [← ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport_eq_biUnion, Q.analyticSupport_cover]

/-- The original scheme frontier proof supplies the analytic frontier containment. -/
theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticSupport_frontier : ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticFrontier Q.pieces :=
  ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesFrontier_analytic Q.pieces Q.frontier

theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.piece_analyticSupport_subset {P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f}
    (hP : P ∈ Q.pieces) : P.analyticSupport ⊆ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' S := by
  intro x hx
  exact Q.piece_support_subset hP hx

/-- Index the same list, without replacing or reordering any geometric piece. -/
def CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.indexedAnalyticSupport (i : Fin Q.pieces.length) :
    Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)) := (Q.pieces.get i).analyticSupport

theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.isLocallyClosed_indexedAnalyticSupport (i : Fin Q.pieces.length) :
    IsLocallyClosed (Q.indexedAnalyticSupport i) :=
  (Q.pieces.get i).isLocallyClosed_analyticSupport

theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.indexedAnalyticSupport_nonempty (i : Fin Q.pieces.length) :
    (Q.indexedAnalyticSupport i).Nonempty :=
  (Q.pieces.get i).analyticSupport_nonempty

theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.finite_range_indexedAnalyticSupport :
    (Set.range Q.indexedAnalyticSupport).Finite := Set.finite_range _

theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.pairwise_indexedAnalyticSupport :
    Pairwise (fun i j => Disjoint (Q.indexedAnalyticSupport i) (Q.indexedAnalyticSupport j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact List.pairwise_iff_get.mp Q.pairwise_disjoint_analyticSupport i j h
  · exact (List.pairwise_iff_get.mp Q.pairwise_disjoint_analyticSupport j i h).symm

theorem CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.indexedAnalyticSupport_iUnion :
    (⋃ i, Q.indexedAnalyticSupport i) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' S := by
  rw [← Q.analyticSupport_biUnion]
  ext x
  simp only [Set.mem_iUnion, CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.indexedAnalyticSupport]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨Q.pieces.get i, List.get_mem _ _, hi⟩
  · rintro ⟨P, hP, hxP⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hP
    exact ⟨i, hxP⟩

end

/-- Apply the partition theorem to the stratification whose existence was proved
from actual finite-type scheme geometry. No stratification is assumed here. -/
theorem ComplexPoints.Analytic.StratificationPointPartition.finiteType_integralSmooth_analyticPartition (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType f] [QuasiCompact f] :
    let Q := CycleClass.Geometric.IntegralSmoothStratification.integralSmoothGeometricStratification_of_finiteType f
    Q.pieces.Pairwise (fun P R => Disjoint P.analyticSupport R.analyticSupport) ∧
      (ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport Q.pieces = Set.univ) ∧
      ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticFrontier Q.pieces := by
  let Q := CycleClass.Geometric.IntegralSmoothStratification.integralSmoothGeometricStratification_of_finiteType f
  refine ⟨Q.pairwise_disjoint_analyticSupport, ?_, Q.analyticSupport_frontier⟩
  simpa only [Set.preimage_univ] using Q.analyticSupport_cover

/-- The actual chosen stratification of any dimension-cycle support partitions
its native complex points, including when the support is singular. -/
theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.integralSmoothGeometricStratification_analytic_cover
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    ComplexPoints.Analytic.StratificationPointPartition.integralSmoothPiecesAnalyticSupport Z.integralSmoothGeometricStratification.pieces =
      Set.univ := by
  simpa only [Set.preimage_univ] using
    Z.integralSmoothGeometricStratification.analyticSupport_cover

end

end OAI.AlgebraicGeometry
