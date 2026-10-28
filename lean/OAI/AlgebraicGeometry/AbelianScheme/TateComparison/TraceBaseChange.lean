import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CorrespondencePointBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TraceAllTests
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricExt

/-! # Trace Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual algebraic correspondence trace commutes with base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {B B' : Scheme.{0}} {X A : Over B} [GrpObj A] [IsCommMonObj A]
  [IsReduced X.left] [IsLocallyNoetherian X.left] [IsSeparated A.hom]
  (C : Correspondences.EtaleCorrespondence X) (p : B' ⟶ B)
  [IsReduced ((Over.pullback p).obj X).left]
  [IsLocallyNoetherian ((Over.pullback p).obj X).left]
  [IsSeparated ((Over.pullback p).obj A).hom]

theorem Correspondences.EtaleCorrespondence.algebraicTrace_baseChange (f : X ⟶ A) :
    (C.baseChange p).algebraicTrace ((Over.pullback p).map f) =
      (Over.pullback p).map (C.algebraicTrace f) := by
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ c x
  classical
  let eA := FieldPointTransport.pointBaseChangeMulEquiv p c (c ≫ p) rfl A
  let x₀ := FieldPointTransport.pointBaseChangeEquiv p c (c ≫ p) rfl X x
  let e := C.baseChangeFiberEquiv p c x
  have : Finite ((C.baseChange p).Fiber x) := Correspondences.EtaleCorrespondence.finiteFiber (C.baseChange p) c x
  let : Fintype ((C.baseChange p).Fiber x) := Fintype.ofFinite _
  let : Fintype (C.Fiber x₀) := Fintype.ofFinite _
  apply eA.injective
  rw [(C.baseChange p).algebraicTrace_geometric, FieldPointTransport.pointBaseChange_comp,
    C.algebraicTrace_geometric]
  change eA (((Finset.univ : Finset ((C.baseChange p).Fiber x)).val.map
    (fun z => (C.baseChange p).endpoint z)).map
      (fun y => y ≫ (Over.pullback p).map f)).prod =
    (((Finset.univ : Finset (C.Fiber x₀)).val.map C.endpoint).map (fun y => y ≫ f)).prod
  rw [map_multiset_prod, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  rw [← Multiset.map_univ_val_equiv e, Multiset.map_map]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro z _
  exact (FieldPointTransport.pointBaseChange_comp p c (c ≫ p) rfl A f _).trans
    (congrArg (· ≫ f) (C.baseChangeFiberEquiv_endpoint p c x z))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
