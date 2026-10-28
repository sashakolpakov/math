import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.EquivalenceCohomology

/-! # Cohomology Finite Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyFiniteDescent

noncomputable section

/-! A finite chain of injections suffices to propagate a later cohomology zero back to its initial term. Thus Serre vanishing along a positive-power subsequence is enough. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem subsingleton_of_injective_sequence_at
    {A : ℕ → Type u} (f : ∀ m, A m → A (m + 1))
    (hf : ∀ m, Function.Injective (f m)) (B : ℕ) (hB : Subsingleton (A B)) : Subsingleton (A 0) := by
  have descend (d : ℕ) : ∀ m, Subsingleton (A (m + d)) → Subsingleton (A m) := by
    induction d with
    | zero => intro m hm; exact hm
    | succ d ih =>
      intro m hm
      have he : (m + 1) + d = m + (d + 1) := by omega
      have hm' : Subsingleton (A (m + 1)) := ih (m + 1) (he.symm ▸ hm)
      exact ⟨fun x y => hf m (hm'.elim (f m x) (f m y))⟩
  exact descend B 0 (by simpa only [Nat.zero_add] using hB)

namespace ZariskiCohomology

theorem coefficientCohomology_vanish_of_iterated_cokernel_at
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    (E : X.Modules ≌ X.Modules) {M : X.Modules} (s : M ⟶ E.functor.obj M) [Mono s] (q B : ℕ)
    (hQ : ∀ m, IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj
      ((Iterated.EquivalenceCohomology.iterateAutoEquivalence E m).functor.obj (cokernel s))))
    (hM : IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj
      ((Iterated.EquivalenceCohomology.iterateAutoEquivalence E B).functor.obj M))) :
    IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj M) := by
  let T : ℕ → X.Modules := fun m => (Iterated.EquivalenceCohomology.iterateAutoEquivalence E m).functor.obj M
  let f : ∀ m, T m ⟶ T (m + 1) := Iterated.EquivalenceCohomology.iterateAutoEquivalenceMap E s
  let H := Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)
  have hmono (m : ℕ) : Mono (f m) := Iterated.EquivalenceCohomology.iterateAutoEquivalenceMap_mono E s m
  have hinj (m : ℕ) : Function.Injective ((H.map (f m)).hom) := by
    have : Mono (f m) := hmono m
    let S : ShortComplex X.Modules := ShortComplex.mk (f m) (cokernel.π (f m)) (cokernel.condition (f m))
    have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact (f m)⟩
    have hcoker : IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj (cokernel (f m))) :=
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).mapIso
        (Iterated.EquivalenceCohomology.iterateAutoEquivalenceCokernelIso E s m)).isZero_iff.mp (hQ m)
    exact CohomologyVanishingDescent.ZariskiCohomology.coefficientCohomology_succ_injective_of_right_zero c hS q hcoker
  have hB : Subsingleton (H.obj (T B)) := ModuleCat.subsingleton_of_isZero hM
  have hzero : Subsingleton (H.obj (T 0)) :=
    subsingleton_of_injective_sequence_at (fun m => (H.map (f m)).hom) hinj B hB
  have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj M) := hzero
  exact ModuleCat.isZero_of_subsingleton _

end ZariskiCohomology

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyFiniteDescent
