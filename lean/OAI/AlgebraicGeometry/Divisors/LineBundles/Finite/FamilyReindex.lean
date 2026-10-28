import Mathlib.Data.Finsupp.Basic

/-! # Family Reindex -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.FamilyReindex.BundleCycles

section

/-!
# LineBundleCycles: summing a finite family through a support-covering embedding

An injective finite indexing set computes the complete sum of a finitely
supported family when its image contains the support. This identifies
the intrinsic residue family with its explicit finite geometric sum.
-/

theorem finiteFamily_sum_embedding {A B M : Type*} [Fintype A] [AddCommMonoid M]
    (i : A ↪ B) (f : B →₀ M) (hf : (f.support : Set B) ⊆ Set.range i) :
    f.sum (fun _ m => m) = ∑ a : A, f (i a) := by
  have h := Finsupp.mapDomain_comapDomain i i.injective f hf
  refine (congrArg (fun q : B →₀ M => q.sum (fun _ m => m)) h).symm.trans ?_
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  exact (Finsupp.comapDomain i f i.injective.injOn).sum_fintype (fun _ m => m) (fun _ => rfl)

end

/-! # LineBundleCycles: reindexing a finite family through any embedding whose image contains its support -/

theorem finiteFamily_sum_comap {A B M : Type*} [AddCommMonoid M]
    (i : A ↪ B) (f : B →₀ M) (hf : (f.support : Set B) ⊆ Set.range i) :
    f.sum (fun _ m => m) = (Finsupp.comapDomain i f i.injective.injOn).sum (fun _ m => m) := by
  have h := Finsupp.mapDomain_comapDomain i i.injective f hf
  refine (congrArg (fun q : B →₀ M => q.sum (fun _ m => m)) h).symm.trans ?_
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.FamilyReindex.BundleCycles
