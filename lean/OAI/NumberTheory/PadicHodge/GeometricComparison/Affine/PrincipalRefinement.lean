import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Principal Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PrincipalRefinement.AffinePrincipalRefinement

noncomputable section

/-! Every covering sieve on an affine spectrum contains an actual finite principal cover whose coefficients generate the unit ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (A : CommRingCat.{u})

def principalArrow (a : A) : (PrimeSpectrum.basicOpen a : (Spec A).Opens) ⟶ (⊤ : (Spec A).Opens) :=
  homOfLE le_top

theorem exists_at (S : Sieve (⊤ : (Spec A).Opens))
    (hS : S ∈ Opens.grothendieckTopology (Spec A) ⊤) (x : PrimeSpectrum A) :
    ∃ a : A, x ∈ PrimeSpectrum.basicOpen a ∧ S (principalArrow A a) := by
  obtain ⟨U, f, hf, hx⟩ := hS x trivial
  obtain ⟨_, ⟨a, rfl⟩, hxa, haU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨a, hxa, ?_⟩
  let g : (PrimeSpectrum.basicOpen a : (Spec A).Opens) ⟶ U := homOfLE haU
  have he : g ≫ f = principalArrow A a :=
    ULift.ext _ _ (Subsingleton.elim _ _)
  exact he ▸ S.downward_closed hf g

theorem finite_refinement (S : Sieve (⊤ : (Spec A).Opens))
    (hS : S ∈ Opens.grothendieckTopology (Spec A) ⊤) :
    ∃ t : Finset A, Ideal.span (t : Set A) = ⊤ ∧ ∀ a ∈ t, S (principalArrow A a) := by
  classical
  choose a ha hmem using exists_at A S hS
  have hs : Ideal.span (Set.range a) = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, ha x⟩
  have h1 : (1 : A) ∈ Ideal.span (Set.range a) := hs ▸ Submodule.mem_top
  obtain ⟨t, ht, h1t⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨t, (Ideal.eq_top_iff_one _).mpr h1t, ?_⟩
  intro b hb
  obtain ⟨x, rfl⟩ := ht hb
  exact hmem x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PrincipalRefinement.AffinePrincipalRefinement
