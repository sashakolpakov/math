import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.JetIdealGenerators
import Mathlib.RingTheory.Unramified.LocalRing

/-! # First Order Unramified -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FirstOrderUnramified

noncomputable section

/-! First-order spanning and normalized coordinate identities imply
the native formally unramified condition on a local homomorphism. -/

set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedCotangent IsLocalRing

universe u v w z

variable {K : Type u} {A : Type v} {R : Type w}
  [Field K] [CommRing A] [CommRing R] [Algebra K A] [Algebra K R]
  [IsLocalRing A] [IsLocalRing R] [IsNoetherianRing R]
  (g : A →ₐ[K] R) (ε : R →ₐ[K] K)

omit [IsLocalRing R] [IsNoetherianRing R] in
theorem centered_mem_image {ι : Type z} (s : ι → R) (r : R)
    (t : ι → A) (ht : ∀ a, r * g (t a) = s a) :
    ∀ a, ε r • s a - ε (s a) • r ∈ (maximalIdeal A).map g.toRingHom := by
  intro a
  let c := ε (g (t a))
  have hc : ε (s a) = ε r * c := by rw [← ht a, map_mul]
  have ha : t a - algebraMap K A c ∈ maximalIdeal A := by
    rw [← AugmentedRegularJet.ideal_eq (ε.comp g)]
    change ε (g (t a - algebraMap K A c)) = 0
    simp [c]
  have hmem : g (t a - algebraMap K A c) ∈ (maximalIdeal A).map g.toRingHom :=
    Ideal.mem_map_of_mem g.toRingHom ha
  have hh := ((maximalIdeal A).map g.toRingHom).mul_mem_left (ε r • r) hmem
  convert hh using 1
  rw [map_sub, g.commutes, hc, ← ht a]
  simp only [Algebra.smul_def, map_mul]
  ring

theorem map_maximalIdeal_eq {ι : Type z} (s : ι → R) (r : R) (hr : ε r ≠ 0)
    (hs : Submodule.span K (Set.range (fun a => AugmentedCotangent.jet ε (s a))) = ⊤)
    (t : ι → A) (ht : ∀ a, r * g (t a) = s a)
    [IsLocalHom g.toRingHom] :
    (maximalIdeal A).map g.toRingHom = maximalIdeal R := by
  apply le_antisymm (IsLocalRing.map_maximalIdeal_le g.toRingHom)
  rw [← JetIdealGenerators.span_maximalIdeal ε r s hr hs]
  apply Ideal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact centered_mem_image g ε s r t ht a

theorem formallyUnramified {ι : Type z} (s : ι → R) (r : R) (hr : ε r ≠ 0)
    (hs : Submodule.span K (Set.range (fun a => AugmentedCotangent.jet ε (s a))) = ⊤)
    (t : ι → A) (ht : ∀ a, r * g (t a) = s a)
    [IsLocalHom g.toRingHom] :
    letI := g.toRingHom.toAlgebra
    Algebra.EssFiniteType A R →
      Algebra.IsSeparable (ResidueField A) (ResidueField R) → Algebra.FormallyUnramified A R := by
  let := g.toRingHom.toAlgebra
  intro hfin hsep
  let := hfin
  let := hsep
  exact Algebra.FormallyUnramified.of_map_maximalIdeal (map_maximalIdeal_eq g ε s r hr hs t ht)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FirstOrderUnramified
