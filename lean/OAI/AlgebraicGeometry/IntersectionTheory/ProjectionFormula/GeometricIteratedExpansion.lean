import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricWeightedEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedTorEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Tor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDimension

/-! # Geometric Iterated Expansion -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricIteratedExpansion

noncomputable section

/-! Expanding the iterated Euler pairing along the top-dimensional
primes of the intermediate intersection gives actual localized Tor
Euler coefficients. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem exists_sum {k : Type} [Field k] {X : Scheme} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) (d : ℕ) [SmoothOfRelativeDimension d f] (x : X)
    (N M L : ModuleCat (X.presheaf.stalk x))
    [Module.Finite (X.presheaf.stalk x) N] [Module.Finite (X.presheaf.stalk x) M]
    [Module.Finite (X.presheaf.stalk x) L] (r s : ℕ)
    (hNM : ∀ p ∈ Module.support (X.presheaf.stalk x) N ∩ Module.support (X.presheaf.stalk x) M,
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f ≤ r)
    (hL : ∀ p ∈ Module.support (X.presheaf.stalk x) L,
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f ≤ s)
    (heq : r + s = d + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f)
    (hi : (Module.support (X.presheaf.stalk x) N ∩ Module.support (X.presheaf.stalk x) M) ∩
      Module.support (X.presheaf.stalk x) L ⊆ {IsLocalRing.closedPoint (X.presheaf.stalk x)}) :
    ∃ F : Finset (PrimeSpectrum (X.presheaf.stalk x)),
      (∀ p ∈ F, p ∈ Module.support (X.presheaf.stalk x) N ∩ Module.support (X.presheaf.stalk x) M ∧
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f = r) ∧
      (∀ p, Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f = r → p ∉ F →
        ProjectionFormula.Tor.Euler.euler (Localization.AtPrime p.asIdeal)
          ((Flat.Extension.baseChange (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal)).obj N)
          ((Flat.Extension.baseChange (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal)).obj M) d = 0) ∧
      (∑ j ∈ Finset.range (d + 1), (-1 : ℚ) ^ j * ProjectionFormula.Tor.Euler.euler (X.presheaf.stalk x)
        (((Tor (ModuleCat (X.presheaf.stalk x)) j).obj N).obj M) L d) =
      ∑ p ∈ F, ProjectionFormula.Tor.Euler.euler (Localization.AtPrime p.asIdeal)
          ((Flat.Extension.baseChange (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal)).obj N)
          ((Flat.Extension.baseChange (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal)).obj M) d *
        ProjectionFormula.Tor.Euler.euler (X.presheaf.stalk x) (.of _ (X.presheaf.stalk x ⧸ p.asIdeal)) L d := by
  let R := X.presheaf.stalk x
  let T (j : ℕ) := ((Tor (ModuleCat R) j).obj N).obj M
  let : ∀ j, Module.Finite R (T j) := fun j => ProjectionFormula.Finite.Tor.finite R N M j
  let : HasProjectiveDimensionLE L d := Smooth.StalkDimension.stalk_bound f d x L
  have hT (j : ℕ) : ∀ p ∈ Module.support R (T j),
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f ≤ r := by
    intro p hp
    exact hNM p (ProjectionFormula.Tor.Support.support_subset R N M j hp)
  choose F hF hout he using (fun j : ℕ => GeometricWeightedEuler.exists_data f d x (T j) r (hT j))
  let U := (Finset.range (d + 1)).biUnion F
  have hU (p : PrimeSpectrum R) (hp : p ∈ U) :
      p ∈ Module.support R N ∩ Module.support R M ∧
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f = r := by
    obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hp
    exact ⟨ProjectionFormula.Tor.Support.support_subset R N M j (hF j p hpj).1, (hF j p hpj).2.1⟩
  have hzero (p : PrimeSpectrum R)
      (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f = r) (hpU : p ∉ U) :
      ProjectionFormula.Tor.Euler.euler (Localization.AtPrime p.asIdeal)
        ((Flat.Extension.baseChange R (Localization.AtPrime p.asIdeal)).obj N)
        ((Flat.Extension.baseChange R (Localization.AtPrime p.asIdeal)).obj M) d = 0 := by
    rw [LocalizedTorEuler.euler]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hout j p hp (fun hpj => hpU (Finset.mem_biUnion.mpr ⟨j, hj, hpj⟩))]
    simp
  refine ⟨U, hU, hzero, ?_⟩
  have hj (j : ℕ) (hj : j ∈ Finset.range (d + 1)) :
      ProjectionFormula.Tor.Euler.euler R (T j) L d =
      ∑ p ∈ U, ((FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) (T j)).toNat : ℚ) *
        ProjectionFormula.Tor.Euler.euler R (.of R (R ⧸ p.asIdeal)) L d := by
    have his : Module.support R (T j) ∩ Module.support R L ⊆ {IsLocalRing.closedPoint R} :=
      (Set.inter_subset_inter_left _ (ProjectionFormula.Tor.Support.support_subset R N M j)).trans hi
    rw [he j L s hL heq his]
    apply Finset.sum_subset (fun p hp => Finset.mem_biUnion.mpr ⟨j, hj, hp⟩)
    intro p hp hpj
    rw [hout j p (hU p hp).2 hpj]
    simp
  calc
    _ = ∑ j ∈ Finset.range (d + 1), ∑ p ∈ U,
        ((-1 : ℚ) ^ j * ((FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) (T j)).toNat : ℚ)) *
          ProjectionFormula.Tor.Euler.euler R (.of R (R ⧸ p.asIdeal)) L d := by
      apply Finset.sum_congr rfl
      intro j hj'
      rw [hj j hj', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [LocalizedTorEuler.euler, Finset.sum_mul]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricIteratedExpansion
