import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms

/-! # Forms Exterior -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormsExterior.PDFormsExterior

noncomputable section

/-!
# Exterior powers of divided-power one-forms

Every PD differential symbol has a canonical interpretation in the exterior
power of the actual PD one-form module. This map is surjective over any
coefficient ring.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

def exteriorSymbol (n : ℕ) (v : Fin n → A) : ⋀[A]^n (DeRham.PDDeRham.Form R A I δ 1) :=
  exteriorPower.ιMulti A n (fun i => OneForms.PDOneForms.D R A I δ (v i))

theorem derivation_tuple_update {n : ℕ} (v : Fin n → A) (i : Fin n) (a : A) :
    (fun j => OneForms.PDOneForms.D R A I δ (Function.update v i a j)) =
      Function.update (fun j => OneForms.PDOneForms.D R A I δ (v j)) i
        (OneForms.PDOneForms.D R A I δ a) := by
  funext j
  by_cases h : j = i <;> simp [h]

theorem exteriorSymbol_update_add {n : ℕ} (v : Fin n → A) (i : Fin n) (a b : A) :
    exteriorSymbol R A I δ n (Function.update v i (a + b)) =
      exteriorSymbol R A I δ n (Function.update v i a) +
        exteriorSymbol R A I δ n (Function.update v i b) := by
  simp only [exteriorSymbol, derivation_tuple_update, map_add, AlternatingMap.map_update_add]

theorem exteriorSymbol_update_mul {n : ℕ} (v : Fin n → A) (i : Fin n) (a b : A) :
    exteriorSymbol R A I δ n (Function.update v i (a * b)) =
      a • exteriorSymbol R A I δ n (Function.update v i b) +
        b • exteriorSymbol R A I δ n (Function.update v i a) := by
  simp only [exteriorSymbol, derivation_tuple_update, Derivation.leibniz,
    AlternatingMap.map_update_add, AlternatingMap.map_update_smul]

theorem exteriorSymbol_update_base {n : ℕ} (v : Fin n → A) (i : Fin n) (r : R) :
    exteriorSymbol R A I δ n (Function.update v i (algebraMap R A r)) = 0 := by
  simp only [exteriorSymbol, derivation_tuple_update, Derivation.map_algebraMap,
    AlternatingMap.map_update_zero]

theorem relation_toExterior {n : ℕ} (r : DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A n) :
    Finsupp.linearCombination A (exteriorSymbol R A I δ n) (DeRhamPresentationTo.DeRhamPresentation.relation R A n r) = 0 := by
  cases r with
  | add v i a b =>
    simp [DeRhamPresentationTo.DeRhamPresentation.relation, exteriorSymbol_update_add]
  | mul v i a b =>
    simp [DeRhamPresentationTo.DeRhamPresentation.relation, exteriorSymbol_update_mul]
  | base v i r =>
    simp [DeRhamPresentationTo.DeRhamPresentation.relation, exteriorSymbol_update_base]
  | alt v i j hij hne =>
    simp only [DeRhamPresentationTo.DeRhamPresentation.relation, Finsupp.linearCombination_single, one_smul, exteriorSymbol]
    exact (exteriorPower.ιMulti A n).map_eq_zero_of_eq _
      (congrArg (OneForms.PDOneForms.D R A I δ) hij) hne

/-- Interpret ordinary differential symbols using the universal PD derivation. -/
def ordinaryMap (n : ℕ) : DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₗ[A] ⋀[A]^n (DeRham.PDDeRham.Form R A I δ 1) :=
  (DeRhamPresentationTo.DeRhamPresentation.relations R A n).liftQ (Finsupp.linearCombination A (exteriorSymbol R A I δ n)) (by
    apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    exact relation_toExterior R A I δ r)

@[simp]
theorem ordinaryMap_symbol {n : ℕ} (a : A) (v : Fin n → A) :
    ordinaryMap R A I δ n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = a • exteriorSymbol R A I δ n v := by
  exact Finsupp.linearCombination_single A a v

theorem ordinaryMap_PDRelation {n : ℕ} (r : DeRham.PDDeRham.RelationIndex A I n) :
    ordinaryMap R A I δ n (DeRham.PDDeRham.relation R A I δ n r) = 0 := by
  simp only [DeRham.PDDeRham.relation, map_sub, ordinaryMap_symbol, one_smul, exteriorSymbol,
    derivation_tuple_update, OneForms.PDOneForms.D_dpow R A I δ r.m r.x.property,
    AlternatingMap.map_update_smul, sub_self]

/-- Interpret PD differential forms in the exterior powers of their actual one-forms. -/
def toExterior (n : ℕ) : DeRham.PDDeRham.Form R A I δ n →ₗ[A] ⋀[A]^n (DeRham.PDDeRham.Form R A I δ 1) :=
  (DeRham.PDDeRham.relations R A I δ n).liftQ (ordinaryMap R A I δ n)
    (Submodule.span_le.mpr (by
      rintro _ ⟨r, rfl⟩
      exact ordinaryMap_PDRelation R A I δ r))

theorem toExterior_symbol {n : ℕ} (a : A) (v : Fin n → A) :
    toExterior R A I δ n (DeRham.PDDeRham.symbol R A I δ a v) = a • exteriorSymbol R A I δ n v :=
  ordinaryMap_symbol R A I δ a v

/-- Exact one-forms span the universal PD one-form module. -/
theorem span_range_D : Submodule.span A (Set.range (OneForms.PDOneForms.D R A I δ)) = ⊤ := by
  let S := Submodule.span A (Set.range (OneForms.PDOneForms.D R A I δ))
  have h : S.mkQ = 0 := by
    apply OneForms.PDOneForms.linearMap_ext R A I δ (DeRham.PDDeRham.Form R A I δ 1 ⧸ S)
    intro a
    exact (Submodule.Quotient.mk_eq_zero S).mpr (Submodule.subset_span (Set.mem_range_self a))
  apply top_unique
  intro ω _
  exact (Submodule.Quotient.mk_eq_zero S).mp (LinearMap.congr_fun h ω)

/-- Every exterior power of PD one-forms is represented by an actual PD form. -/
theorem toExterior_surjective (n : ℕ) : Function.Surjective (toExterior R A I δ n) := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← exteriorPower.ιMulti_span_of_span A n (DeRham.PDDeRham.Form R A I δ 1) (span_range_D R A I δ)]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  have h (i : Fin n) : ∃ a : A, OneForms.PDOneForms.D R A I δ a = v i := hv (Set.mem_range_self i)
  choose a ha using h
  refine ⟨DeRham.PDDeRham.symbol R A I δ 1 a, ?_⟩
  rw [toExterior_symbol, one_smul]
  unfold exteriorSymbol
  congr 1
  funext i
  exact ha i

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormsExterior.PDFormsExterior
