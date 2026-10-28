import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseQuotient

/-! # Forms Base Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseExtension

noncomputable section

/-!
# IntegralComparison: canonical extension of the base for actual PD differential forms

Extending the base imposes the additional constant differential
relations. The resulting canonical maps on the actual form modules
commute with the de Rham differential, without a flatness assumption.
-/

universe u

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

def ordinaryMap (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S A n :=
  (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n).liftQ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations S A n).mkQ
    (fun _ h => Submodule.Quotient.mk_eq_zero _ |>.mpr
      (FormsBaseQuotient.ordinaryRelations_le R S A n h))

theorem ordinaryMap_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    ordinaryMap R S A n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S A a v := rfl

theorem ordinaryMap_differential (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    ordinaryMap R S A (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S A n (ordinaryMap R S A n ω) := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | single v a =>
    change ordinaryMap R S A (n + 1)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S A n (ordinaryMap R S A n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
    rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential_symbol, ordinaryMap_symbol,
      ordinaryMap_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential_symbol]

variable (I : Ideal A) (δ : DividedPowers I)

theorem ordinaryMap_relation (n : ℕ) (r : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.RelationIndex A I n) :
    ordinaryMap R S A n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation R A I δ n r) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation S A I δ n r := by
  simp only [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation, map_sub, ordinaryMap_symbol]

theorem ordinaryMap_relations (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n)
    (hω : ω ∈ AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ n) :
    ordinaryMap R S A n ω ∈ AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations S A I δ n := by
  induction hω using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨r, rfl⟩ := hω
    rw [ordinaryMap_relation]
    exact Submodule.subset_span (Set.mem_range_self r)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add ω η hω hη ihω ihη => rw [map_add]; exact Submodule.add_mem _ ihω ihη
  | smul a ω hω ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

def formsMap (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form S A I δ n :=
  (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ n).liftQ
    ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations S A I δ n).mkQ.comp (ordinaryMap R S A n))
    (fun ω hω => Submodule.Quotient.mk_eq_zero _ |>.mpr
      (ordinaryMap_relations R S A I δ n ω hω))

theorem formsMap_mk (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formsMap R S A I δ n ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ n).mkQ ω) =
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations S A I δ n).mkQ (ordinaryMap R S A n ω) := rfl

theorem formsMap_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    formsMap R S A I δ n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ a v) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol S A I δ a v := rfl

theorem formsMap_differential (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n) :
    formsMap R S A I δ (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential S A I δ n (formsMap R S A I δ n ω) := by
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ n) ω
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential_mk, formsMap_mk, formsMap_mk,
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential_mk, ordinaryMap_differential]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseExtension
