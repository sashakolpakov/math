import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Neighbors

/-! # Branch Enumeration -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.BranchEnumeration.CM

/-! Relabel the actual correspondence branches without changing their
target multiset. Precomposition preserves each original target map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Neighbors

variable {B : Scheme} {X : Over B} (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
  {T U : Over B} (p : U ⟶ T) (x : T ⟶ X)

def precomposeBranch (z : C.Fiber x) : C.Fiber (p ≫ x) :=
  ⟨p ≫ z.val, (Category.assoc _ _ _).trans (congrArg (p ≫ ·) z.property)⟩

theorem precomposeBranch_endpoint (z : C.Fiber x) :
    C.endpoint (precomposeBranch C p x z) = p ≫ C.endpoint z := Category.assoc _ _ _

theorem precomposeBranch_injective [Epi p] : Function.Injective (precomposeBranch C p x) := by
  intro z w h
  apply Subtype.ext
  exact (cancel_epi p).mp (congrArg Subtype.val h)

variable {k : Type} [Field k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ B) (y : Over.mk b ⟶ X)
  {I : Type} [Fintype I] (e : I ≃ C.Fiber y)

theorem neighbors_eq_enumerated_targets :
    C.neighbors b y = (Finset.univ : Finset I).val.map (fun i => C.endpoint (e i)) := by
  classical
  let : Fintype (C.Fiber y) := Fintype.ofFinite _
  change (Finset.univ : Finset (C.Fiber y)).val.map C.endpoint = _
  rw [← Multiset.map_univ_val_equiv e, Multiset.map_map]
  rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.BranchEnumeration.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.BranchEnumeration.CM.TestIso

/-! Isomorphic tests and equal source points identify the actual branch
fibers. The identifications preserve their actual endpoint maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Neighbors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BranchEnumeration.CM

variable {B : Scheme} {X : Over B} (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
  {T U : Over B} (e : U ≅ T) (x : T ⟶ X)

def testEquiv : C.Fiber x ≃ C.Fiber (e.hom ≫ x) where
  toFun := precomposeBranch C e.hom x
  invFun z := ⟨e.inv ≫ z.val, by
    rw [Category.assoc, z.property, e.inv_hom_id_assoc]⟩
  left_inv z := by
    apply Subtype.ext
    exact e.inv_hom_id_assoc z.val
  right_inv z := by
    apply Subtype.ext
    exact e.hom_inv_id_assoc z.val

theorem testEquiv_endpoint (z : C.Fiber x) :
    C.endpoint (testEquiv C e x z) = e.hom ≫ C.endpoint z :=
  precomposeBranch_endpoint C e.hom x z

def sourceEquiv {x₀ y₀ : T ⟶ X} (h : x₀ = y₀) : C.Fiber x₀ ≃ C.Fiber y₀ :=
  h ▸ Equiv.refl (C.Fiber x₀)

theorem sourceEquiv_endpoint {x₀ y₀ : T ⟶ X} (h : x₀ = y₀) (z : C.Fiber x₀) :
    C.endpoint (sourceEquiv C h z) = C.endpoint z := by
  subst y₀
  rfl

def labels {I : Type} (eLabels : I ≃ C.Fiber x) {y : U ⟶ X} (hy : e.hom ≫ x = y) :
    I ≃ C.Fiber y := eLabels.trans ((testEquiv C e x).trans (sourceEquiv C hy))

theorem labels_endpoint {I : Type} (eLabels : I ≃ C.Fiber x) {y : U ⟶ X}
    (hy : e.hom ≫ x = y) (i : I) :
    C.endpoint (labels C e x eLabels hy i) = e.hom ≫ C.endpoint (eLabels i) :=
  (sourceEquiv_endpoint C hy (testEquiv C e x (eLabels i))).trans
    (testEquiv_endpoint C e x (eLabels i))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.BranchEnumeration.CM.TestIso

end

end OAI
