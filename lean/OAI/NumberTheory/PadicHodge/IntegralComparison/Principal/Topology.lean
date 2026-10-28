import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Topology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Topology

noncomputable section

/-!
# IntegralComparison: the principal-open basis carries the actual Zariski topology

The principal-open functor is fully faithful and cover dense. Its induced
topology has exactly the point-covering sieves, and sheaves on this basis
are equivalent to sheaves on the entire affine Zariski space.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens.Category

universe u v w

variable (R : Type u) [CommRing R]

instance toOpens_faithful : (PrincipalOpens.Category.toOpens R).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance toOpens_full : (PrincipalOpens.Category.toOpens R).Full where
  map_surjective a := ⟨homOfLE (leOfHom a), Subsingleton.elim _ _⟩

instance toOpens_coverDense : (PrincipalOpens.Category.toOpens R).IsCoverDense (Opens.grothendieckTopology (PrimeSpectrum R)) where
  is_cover := by
    intro V z hz
    obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz V.isOpen
    exact ⟨PrimeSpectrum.basicOpen r, homOfLE hsub,
      ⟨PrincipalOpens.Category.Principal.mk r, 𝟙 _, homOfLE hsub, rfl⟩, hr⟩

def topology : GrothendieckTopology (PrincipalOpens.Category.Principal R) :=
  (PrincipalOpens.Category.toOpens R).inducedTopology (Opens.grothendieckTopology (PrimeSpectrum R))

theorem covering_iff {r : PrincipalOpens.Category.Principal R} (S : Sieve r) : S ∈ topology R r ↔
    ∀ z ∈ PrimeSpectrum.basicOpen r.function,
      ∃ (s : PrincipalOpens.Category.Principal R) (a : s ⟶ r), S a ∧ z ∈ PrimeSpectrum.basicOpen s.function := by
  rw [topology, Functor.mem_inducedTopology_iff_of_isCoverDense]
  apply forall₂_congr
  intro z hz
  constructor
  · rintro ⟨V, a, ⟨s, b, c, hb, rfl⟩, hV⟩
    exact ⟨s, b, hb, (leOfHom c) hV⟩
  · rintro ⟨s, a, ha, hs⟩
    exact ⟨(PrincipalOpens.Category.toOpens R).obj s, (PrincipalOpens.Category.toOpens R).map a,
      ⟨s, a, 𝟙 _, ha, Subsingleton.elim _ _⟩, hs⟩

variable (A : Type v) [Category.{w} A]
  [∀ V : (Opens (PrimeSpectrum R))ᵒᵖ, HasLimitsOfShape (StructuredArrow V (PrincipalOpens.Category.toOpens R).op) A]

/-- Actual Zariski sheaves can be computed on the principal-open category. -/
def sheafEquiv : Sheaf (topology R) A ≌ Sheaf (Opens.grothendieckTopology (PrimeSpectrum R)) A :=
  (PrincipalOpens.Category.toOpens R).sheafInducedTopologyEquivOfIsCoverDense _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Topology
