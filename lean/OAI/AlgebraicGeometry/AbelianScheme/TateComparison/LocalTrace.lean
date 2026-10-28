import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BranchFibers
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricExt
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Local Trace -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Local algebraic trace maps are sums of actual branches. Their
geometric values count all fiber points and imply overlap compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {B : Scheme.{0}} {X A : Over B} [GrpObj A] [IsCommMonObj A]
  (C : Correspondences.EtaleCorrespondence X) (f : X ⟶ A)

/-- Precomposition preserves the actual commutative group law on points. -/
def Correspondences.EtaleCorrespondence.precompPointHom {T T' : Over B} (a : T' ⟶ T) : (T ⟶ A) →* (T' ⟶ A) where
  toFun g := a ≫ g
  map_one' := MonObj.comp_one a
  map_mul' := MonObj.comp_mul a

/-- The group-object notation writes the additive trace as a product. -/
def Correspondences.EtaleCorrespondence.localTraceMap {T : Over B} (x : T ⟶ X) {n : ℕ} (e : C.BranchSplitting x n) : T ⟶ A :=
  ∏ i : Fin n, C.endpoint (C.splitBranch x e i) ≫ f

/-- The geometric trace counts every actual source-fiber point, including
distinct branches whose endpoints coincide. -/
def Correspondences.EtaleCorrespondence.geometricTrace {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ B) (x : Over.mk b ⟶ X) : Over.mk b ⟶ A :=
  ((C.neighbors b x).map (fun y => y ≫ f)).prod

theorem Correspondences.EtaleCorrespondence.localTraceMap_geometric {T : Over B} (x : T ⟶ X) {n : ℕ}
    (e : C.BranchSplitting x n) {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ B) (a : Over.mk b ⟶ T) :
    a ≫ C.localTraceMap f x e = C.geometricTrace f b (a ≫ x) := by
  classical
  let : Fintype (C.Fiber (a ≫ x)) := Fintype.ofFinite _
  calc
    a ≫ C.localTraceMap f x e =
        ∏ i : Fin n, C.endpoint (C.splitFiberEquiv x a e i) ≫ f := by
      change Correspondences.EtaleCorrespondence.precompPointHom a (∏ i : Fin n, C.endpoint (C.splitBranch x e i) ≫ f) = _
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro i _
      exact (Category.assoc a _ f).symm.trans
        (congrArg (fun z => z ≫ f) (C.splitFiberEquiv_endpoint x a e i).symm)
    _ = ∏ c : C.Fiber (a ≫ x), C.endpoint c ≫ f :=
      (C.splitFiberEquiv x a e).prod_comp (fun c => C.endpoint c ≫ f)
    _ = C.geometricTrace f b (a ≫ x) := by
      simp only [Correspondences.EtaleCorrespondence.geometricTrace, Correspondences.EtaleCorrespondence.neighbors, Multiset.map_map, Function.comp_def]
      rfl

/-- Two actual local splittings give the same algebraic trace map on a
reduced test scheme with separated target. -/
theorem Correspondences.EtaleCorrespondence.localTraceMap_independent {T : Over B} [IsReduced T.left] [IsSeparated A.hom]
    (x : T ⟶ X) {n m : ℕ} (e : C.BranchSplitting x n) (e' : C.BranchSplitting x m) :
    C.localTraceMap f x e = C.localTraceMap f x e' := by
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b a
  rw [Correspondences.EtaleCorrespondence.localTraceMap_geometric, Correspondences.EtaleCorrespondence.localTraceMap_geometric]

/-- The local traces agree on every reduced overlap. The compatibility
is proved from the actual geometric fibers, for arbitrary choices of splitting. -/
theorem Correspondences.EtaleCorrespondence.localTraceMap_overlap {T T' W : Over B} [IsReduced W.left] [IsSeparated A.hom]
    (x : T ⟶ X) (x' : T' ⟶ X) {n m : ℕ}
    (e : C.BranchSplitting x n) (e' : C.BranchSplitting x' m)
    (a : W ⟶ T) (a' : W ⟶ T') (h : a ≫ x = a' ≫ x') :
    a ≫ C.localTraceMap f x e = a' ≫ C.localTraceMap f x' e' := by
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b z
  rw [← Category.assoc, ← Category.assoc, Correspondences.EtaleCorrespondence.localTraceMap_geometric, Correspondences.EtaleCorrespondence.localTraceMap_geometric,
    Category.assoc, Category.assoc, h]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
