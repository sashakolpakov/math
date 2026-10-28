import OAI.LinearAlgebra.Endomorphisms.Commuting
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters

/-! # Character Refinement -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CharacterRefinement.Spectral

noncomputable section

section

/-! Full simultaneous generalized eigenspaces refine every restricted
commuting family. This constructs occurring full extensions and retains
the whole restricted eigenspace, including all multiplicities. -/

open scoped Classical

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM

variable {K V I J : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem jointSpace_restriction_le (T : J → Module.End K V) (u : I → J) (ψ : J → K) :
    HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace T ψ ≤ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (T ∘ u) (ψ ∘ u) := by
  exact le_iInf fun i => iInf_le _ (u i)

theorem jointSpace_full_refinement [IsAlgClosed K] [FiniteDimensional K V]
    (T : J → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j))
    (u : I → J) (χ : I → K) :
    HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (T ∘ u) χ =
      ⨆ ψ : {ψ : J → K // ∀ i, ψ (u i) = χ i}, HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace T ψ.val := by
  obtain ⟨_, _, _, hfinite, hind, hspan, _⟩ :=
    LinearAlgebra.Endomorphisms.Commuting.Construction.commuting_family_structure T hcomm
  let O := {ψ : J → K // HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace T ψ ≠ ⊥}
  let : Fintype O := hfinite.fintype
  let S : O → Submodule K V := fun ψ => HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace T ψ.val
  have hS : DirectSum.IsInternal S := HeckeCycles.HeckeCharacters.CM.Projectors.joint_internal_of_Commuting T hind hspan
  have hc (ψ : O) (j : J) : Commute (HeckeCycles.HeckeCharacters.CM.Projectors.projector S hS ψ) (T j) :=
    HeckeCycles.HeckeCharacters.CM.Projectors.projector_commutes S hS (T j)
      (fun k _ hx => HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace_stable_of_commutes T k.val (T j) (fun l => hcomm l j) hx) ψ
  apply le_antisymm
  · intro x hx
    rw [← HeckeCycles.HeckeCharacters.CM.Projectors.sum_projector S hS x]
    apply Submodule.sum_mem
    intro ψ _
    by_cases hp : ∀ i, ψ.val (u i) = χ i
    · exact (le_iSup (fun φ : {ψ : J → K // ∀ i, ψ (u i) = χ i} => HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace T φ.val)
        ⟨ψ.val, hp⟩) (HeckeCycles.HeckeCharacters.CM.Projectors.projector_mem S hS ψ x)
    · have hne : ψ.val ∘ u ≠ χ := fun he => hp (congrFun he)
      have hleft := jointSpace_restriction_le T u ψ.val (HeckeCycles.HeckeCharacters.CM.Projectors.projector_mem S hS ψ x)
      have hright := HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace_stable_of_commutes (T ∘ u) χ (HeckeCycles.HeckeCharacters.CM.Projectors.projector S hS ψ)
        (fun i => (hc ψ (u i)).symm) hx
      have hz := Submodule.disjoint_def.mp (HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace_disjoint (T ∘ u) hne)
        _ hleft hright
      rw [hz]
      exact Submodule.zero_mem _
  · apply iSup_le
    intro ψ
    have he : ψ.val ∘ u = χ := funext ψ.property
    simpa only [he] using jointSpace_restriction_le T u ψ.val

theorem exists_occurring_full_extension [IsAlgClosed K] [FiniteDimensional K V]
    (T : J → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j))
    (u : I → J) (χ : I → K) (hχ : HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (T ∘ u) χ ≠ ⊥) :
    ∃ ψ : J → K, (∀ i, ψ (u i) = χ i) ∧ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace T ψ ≠ ⊥ := by
  by_contra hn
  apply hχ
  rw [jointSpace_full_refinement T hcomm u χ]
  apply iSup_eq_bot.mpr
  intro ψ
  by_contra hp
  exact hn ⟨ψ.val, ψ.property, hp⟩

/-- The functions in the full decomposition are genuine characters over
all coefficient scalars, with exactly the same values. -/
def fullJointCharacter {H : Type*} [CommRing H] [Algebra K H]
    (ρ : H →ₐ[K] Module.End K V) (χ : H → K)
    (hχ : HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace ρ χ ≠ ⊥) : H →ₐ[K] K where
  __ := HeckeCycles.HeckeCharacters.CM.jointRingCharacter ρ.toRingHom χ hχ
  commutes' c := HeckeCycles.HeckeCharacters.CM.character_scalar ρ.toRingHom χ hχ (algebraMap K H c) c
    (by
      change ρ (algebraMap K H c) = c • 1
      rw [ρ.commutes, Algebra.algebraMap_eq_smul_one])

theorem jointSpace_full_character_refinement
    [IsAlgClosed K] [FiniteDimensional K V]
    {H : Type*} [CommRing H] [Algebra K H]
    (ρ : H →ₐ[K] Module.End K V) (u : I → H) (χ : I → K) :
    HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (ρ ∘ u) χ =
      ⨆ ψ : {ψ : H →ₐ[K] K // ∀ i, ψ (u i) = χ i}, HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace ρ ψ.val := by
  rw [jointSpace_full_refinement ρ (fun a b => (Commute.all a b).map ρ) u χ]
  apply le_antisymm
  · apply iSup_le
    intro ψ
    by_cases hz : HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace ρ ψ.val = ⊥
    · rw [hz]
      exact bot_le
    · exact le_iSup_of_le ⟨fullJointCharacter ρ ψ.val hz, ψ.property⟩ le_rfl
  · apply iSup_le
    intro ψ
    exact le_iSup_of_le ⟨ψ.val, ψ.property⟩ le_rfl

theorem exists_occurring_full_character
    [IsAlgClosed K] [FiniteDimensional K V]
    {H : Type*} [CommRing H] [Algebra K H]
    (ρ : H →ₐ[K] Module.End K V) (u : I → H) (χ : I → K)
    (hχ : HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (ρ ∘ u) χ ≠ ⊥) :
    ∃ ψ : H →ₐ[K] K, (∀ i, ψ (u i) = χ i) ∧ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace ρ ψ ≠ ⊥ := by
  obtain ⟨ψ, hp, hn⟩ := exists_occurring_full_extension ρ
    (fun a b => (Commute.all a b).map ρ) u χ hχ
  exact ⟨fullJointCharacter ρ ψ hn, hp, hn⟩

end

/-! Scalar extension adds no generalized eigenconditions beyond the
rational Hecke operators and the character's scalar-linearity. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors

variable {F H V : Type*} [Field F] [Algebra ℚ F] [CommRing H] [Algebra ℚ H]
  [AddCommGroup V] [Module F V]

theorem jointSpace_scalar_extension (ρ : F ⊗[ℚ] H →ₐ[F] Module.End F V)
    (χ : F ⊗[ℚ] H →ₐ[F] F) :
    HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace ρ χ = HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h : H => ρ (1 ⊗ₜ[ℚ] h))
      (fun h : H => χ (1 ⊗ₜ[ℚ] h)) := by
  apply le_antisymm
  · exact jointSpace_restriction_le ρ (fun h : H => (1 : F) ⊗ₜ[ℚ] h) χ
  · intro x hx
    simp only [HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace, Submodule.mem_iInf] at hx ⊢
    intro h
    induction h using TensorProduct.inductionOn with
    | tmul c h =>
      have he : c ⊗ₜ[ℚ] h = c • ((1 : F) ⊗ₜ[ℚ] h) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he, map_smul, map_smul]
      exact Module.End.genEigenspace_le_smul (ρ (1 ⊗ₜ[ℚ] h)) (χ (1 ⊗ₜ[ℚ] h)) c ⊤ (hx h)
    | add h k hh hk =>
      have hc := (Commute.all h k).map ρ
      have hm := Module.End.genEigenspace_inf_le_add (ρ h) (ρ k) (χ h) (χ k) ⊤ ⊤ hc
      simpa only [map_add, top_add] using hm ⟨hh, hk⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CharacterRefinement.Spectral
