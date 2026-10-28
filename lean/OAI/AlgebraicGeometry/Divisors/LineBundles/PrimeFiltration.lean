import OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeSubquotient

/-! # Prime Filtration -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeFiltration.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite prime filtrations constructed from Noetherianity

The filtration stores actual submodules, strict inclusions, prime ideals,
and isomorphisms of the successive quotients with R/p. Noetherian
induction constructs a finite such filtration above every submodule.
This supplies the finite reduction used by local intersection lengths.
-/

universe u v
variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- A concrete finite sequence of prime cyclic factors from N to the full module. -/
inductive PrimeFiltrationAbove : Submodule R M → Type (max u v) where
  | top : PrimeFiltrationAbove ⊤
  | step (N L : Submodule R M) (hNL : N < L) (J : Ideal R) (hJ : J.IsPrime)
      (factor : (L ⧸ N.comap L.subtype) ≃ₗ[R] R ⧸ J)
      (tail : PrimeFiltrationAbove L) : PrimeFiltrationAbove N

namespace PrimeFiltrationAbove

def length {N : Submodule R M} : BundleCycles.PrimeFiltrationAbove N → ℕ
  | .top => 0
  | .step _ _ _ _ _ _ tail => tail.length + 1

def factors {N : Submodule R M} : BundleCycles.PrimeFiltrationAbove N → List (Ideal R)
  | .top => []
  | .step _ _ _ J _ _ tail => J :: tail.factors

theorem factors_length {N : Submodule R M} (F : BundleCycles.PrimeFiltrationAbove N) : F.factors.length = F.length := by
  induction F with
  | top => rfl
  | step N L hNL J hJ e tail ih => exact congrArg Nat.succ ih

theorem factor_isPrime {N : Submodule R M} (F : BundleCycles.PrimeFiltrationAbove N) (J : Ideal R)
    (hJ : J ∈ F.factors) : J.IsPrime := by
  induction F with
  | top => exact False.elim (List.not_mem_nil hJ)
  | step N L hNL K hK e tail ih =>
    rcases List.mem_cons.mp hJ with rfl | h
    · exact hK
    · exact ih h

end PrimeFiltrationAbove

/-- Actual prime cyclic factors and Noetherian induction provide a finite filtration. -/
theorem primeFiltrationAbove_nonempty [IsNoetherianRing R] [IsNoetherian R M] (N : Submodule R M) :
    Nonempty (BundleCycles.PrimeFiltrationAbove N) := by
  refine IsNoetherian.induction (P := fun N => Nonempty (BundleCycles.PrimeFiltrationAbove N)) ?_ N
  intro N ih
  by_cases hN : N = ⊤
  · subst N
    exact ⟨.top⟩
  · obtain ⟨L, J, hNL, hJ, ⟨e⟩⟩ := PrimeSubquotient.BundleCycles.exists_prime_cyclic_subquotient N hN
    exact ⟨.step N L hNL J hJ e (Classical.choice (ih L hNL))⟩

/-- A chosen concrete prime filtration of the whole Noetherian module. -/
def modulePrimeFiltration [IsNoetherianRing R] [IsNoetherian R M] : BundleCycles.PrimeFiltrationAbove (⊥ : Submodule R M) :=
  Classical.choice (primeFiltrationAbove_nonempty ⊥)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeFiltration.BundleCycles
