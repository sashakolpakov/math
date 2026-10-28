import OAI.RepresentationTheory.Theta.Geometric.UnramifiedJacobianCriterion
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Cotangent Relation Bound -/

namespace OAI.RepresentationTheory.Theta.Geometric.CotangentRelationBound

noncomputable section

/-! A finite set of original ideal generators bounds the residue
cotangent dimension. For an unramified quotient this yields smoothness
when there are no more equations than ambient relative coordinates. -/

open scoped TensorProduct
open KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] (P : Algebra.Extension R S)

theorem cotangent_residue_finrank_le_generators {n : ℕ} (r : Fin n → P.Ring)
    (hr : Ideal.span (Set.range r) = P.ker) :
    Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] P.Cotangent) ≤ n := by
  let v : Fin n → P.Cotangent := fun i => Algebra.Extension.Cotangent.mk
    ⟨r i, hr.le (Ideal.subset_span ⟨i, rfl⟩)⟩
  let f := Finsupp.linearCombination S v
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker r hr
  have ht : Function.Surjective (f.baseChange (IsLocalRing.ResidueField S)) :=
    LinearMap.lTensor_surjective (IsLocalRing.ResidueField S) hf
  have h := LinearMap.finrank_le_finrank_of_surjective ht
  change Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] P.Cotangent) ≤
    Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] (Fin n →₀ S)) at h
  simpa only [Module.finrank_baseChange, Module.finrank_finsupp_self, Fintype.card_fin] using h

variable [Algebra.FormallySmooth R P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄R]] [Module.Finite P.Ring Ω[P.Ring⁄R]]
    [Algebra.FormallyUnramified R S]

omit [Algebra.FormallySmooth R P.Ring] [Module.Finite P.Ring Ω[P.Ring⁄R]]
    [Algebra.FormallyUnramified R S] in
theorem cotangentSpace_residue_finrank :
    Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] P.CotangentSpace) =
      Module.finrank P.Ring Ω[P.Ring⁄R] := by
  have : Nontrivial P.Ring := RingHom.domain_nontrivial (algebraMap P.Ring S)
  rw [Module.finrank_baseChange]
  change Module.finrank S (S ⊗[P.Ring] Ω[P.Ring⁄R]) = _
  rw [Module.finrank_baseChange]

include P in
theorem formallySmooth_of_unramified_few_equations {n : ℕ} (r : Fin n → P.Ring)
    (hr : Ideal.span (Set.range r) = P.ker)
    (hn : n ≤ Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] P.CotangentSpace)) :
    Algebra.FormallySmooth R S := by
  have hI : P.ker.FG := hr ▸ Submodule.fg_span (Set.finite_range r)
  exact UnramifiedJacobianCriterion.formallySmooth_of_unramified_cotangent_bound P hI
    ((cotangent_residue_finrank_le_generators P r hr).trans hn)

include P in
theorem formallySmooth_of_unramified_ambient_rank {n : ℕ} (r : Fin n → P.Ring)
    (hr : Ideal.span (Set.range r) = P.ker)
    (hn : n ≤ Module.finrank P.Ring Ω[P.Ring⁄R]) : Algebra.FormallySmooth R S :=
  formallySmooth_of_unramified_few_equations P r hr
    (hn.trans_eq (cotangentSpace_residue_finrank P).symm)

end

end OAI.RepresentationTheory.Theta.Geometric.CotangentRelationBound
