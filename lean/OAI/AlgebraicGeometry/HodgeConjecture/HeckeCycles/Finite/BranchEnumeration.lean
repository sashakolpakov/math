import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BranchEnumeration

/-! # Branch Enumeration -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BranchEnumeration.CM

noncomputable section

/-! If the actual branch fibers over two field tests have the same
finite cardinality, field-extension injectivity makes the original
labels exhaustive after extension. This preserves each actual target;
no naturality assumption on the independently constructed labels is needed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BranchEnumeration.CM

variable {B : Scheme} {X : Over B} (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
  {T U : Over B} (p : U ⟶ T) [Epi p] (x : T ⟶ X)
  {I : Type} [Fintype I] (e : I ≃ C.Fiber x) (e' : I ≃ C.Fiber (p ≫ x))

include e e' in
theorem precompose_bijective : Function.Bijective (BranchEnumeration.CM.precomposeBranch C p x) := by
  let : Fintype (C.Fiber x) := Fintype.ofEquiv I e
  let : Fintype (C.Fiber (p ≫ x)) := Fintype.ofEquiv I e'
  apply (Fintype.bijective_iff_injective_and_card (BranchEnumeration.CM.precomposeBranch C p x)).mpr
  exact ⟨BranchEnumeration.CM.precomposeBranch_injective C p x, (Fintype.card_congr e).symm.trans (Fintype.card_congr e')⟩

def extensionEquiv : C.Fiber x ≃ C.Fiber (p ≫ x) :=
  Equiv.ofBijective (BranchEnumeration.CM.precomposeBranch C p x) (precompose_bijective C p x e e')

def extendedLabels : I ≃ C.Fiber (p ≫ x) := e.trans (extensionEquiv C p x e e')

theorem extendedLabels_endpoint (i : I) :
    C.endpoint (extendedLabels C p x e e' i) = p ≫ C.endpoint (e i) :=
  BranchEnumeration.CM.precomposeBranch_endpoint C p x (e i)

variable {k : Type} [Field k] [IsAlgClosed k]

theorem neighbors_eq_original_targets
    (b : Spec (.of k) ⟶ B) (pU : Over.mk b ⟶ T) [Epi pU]
    (eU : I ≃ C.Fiber (pU ≫ x)) :
    C.neighbors b (pU ≫ x) =
      (Finset.univ.val.map (fun i => C.endpoint (e i))).map (fun y => pU ≫ y) := by
  rw [BranchEnumeration.CM.neighbors_eq_enumerated_targets C b (pU ≫ x) (extendedLabels C pU x e eU)]
  simp only [Multiset.map_map, Function.comp_def, extendedLabels_endpoint]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BranchEnumeration.CM
