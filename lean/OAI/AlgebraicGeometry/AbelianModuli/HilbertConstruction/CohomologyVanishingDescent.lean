import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.ExactPairs

/-! # Cohomology Vanishing Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyVanishingDescent

noncomputable section

/-! Exact cohomology sequences propagate eventual vanishing backwards through a sequence of injections when the preceding cohomology of their actual cokernels vanishes. This is the homological step in a hyperplane-section upper-bound argument. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem subsingleton_sequence_of_injective_of_eventually
    {A : ℕ → Type u} (f : ∀ m, A m → A (m + 1))
    (hf : ∀ m, Function.Injective (f m))
    (h : ∃ B, ∀ m, B ≤ m → Subsingleton (A m)) : ∀ m, Subsingleton (A m) := by
  have descend (d : ℕ) : ∀ m, Subsingleton (A (m + d)) → Subsingleton (A m) := by
    induction d with
    | zero => intro m hm; exact hm
    | succ d ih =>
      intro m hm
      have he : (m + 1) + d = m + (d + 1) := by omega
      have hm' : Subsingleton (A (m + 1)) := ih (m + 1) (he.symm ▸ hm)
      exact ⟨fun x y => hf m (hm'.elim (f m x) (f m y))⟩
  obtain ⟨B, hB⟩ := h
  intro m
  exact descend B m (hB (m + B) (Nat.le_add_left B m))

namespace ZariskiCohomology
variable {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))

theorem coefficientCohomology_succ_injective_of_right_zero
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ)
    (hright : IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj S.X₃)) :
    Function.Injective (((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).map S.f).hom) := by
  let f := ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).map S.f).hom
  let δ := (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap c hS n).hom
  have hz : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj S.X₃) :=
    ModuleCat.subsingleton_of_isZero hright
  change Function.Injective f
  intro x y hxy
  have hsub : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨z, hδ⟩ := (CoefficientCohomology.ExactPairs.ZariskiCohomology.coefficientCohomology_exact_left c hS n (x - y)).mp hsub
  have hzero : x - y = 0 := hδ.symm.trans
    ((congrArg δ (hz.elim z 0)).trans δ.map_zero)
  exact sub_eq_zero.mp hzero

theorem coefficientCohomology_vanish_of_eventual_twists
    (M : ℕ → X.Modules) (s : ∀ m, M m ⟶ M (m + 1))
    (hs : ∀ m, Mono (s m)) (n : ℕ)
    (hcoker : ∀ m, IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj (cokernel (s m))))
    (heventual : ∃ B, ∀ m, B ≤ m → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).obj (M m))) :
    ∀ m, IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).obj (M m)) := by
  let H := Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)
  let f (m : ℕ) : H.obj (M m) → H.obj (M (m + 1)) := (H.map (s m)).hom
  have hf (m : ℕ) : Function.Injective (f m) := by
    have : Mono (s m) := hs m
    let S : ShortComplex X.Modules := ShortComplex.mk (s m) (cokernel.π (s m)) (cokernel.condition (s m))
    have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact (s m)⟩
    exact coefficientCohomology_succ_injective_of_right_zero c hS n (hcoker m)
  have h : ∃ B, ∀ m, B ≤ m → Subsingleton (H.obj (M m)) := by
    obtain ⟨B, hB⟩ := heventual
    exact ⟨B, fun m hm => ModuleCat.subsingleton_of_isZero (hB m hm)⟩
  intro m
  have : Subsingleton (H.obj (M m)) := subsingleton_sequence_of_injective_of_eventually f hf h m
  exact ModuleCat.isZero_of_subsingleton _

end ZariskiCohomology

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyVanishingDescent
