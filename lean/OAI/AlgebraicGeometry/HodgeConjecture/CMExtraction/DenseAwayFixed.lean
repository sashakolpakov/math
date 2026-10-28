import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseOpenRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.EigenlineCharacter

/-! # Dense Away Fixed -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseAwayFixed.TestTransport

noncomputable section

/-! Exact fixedness on an away level follows from its preserved line,
the dense perfect active factor, and exact fixedness over an open
active subgroup. No continuity of the scalar action is required. -/

open scoped Classical

variable {Γ G H K V : Type*} [Group Γ] [Group G] [Group H]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H]
  [Field K] [AddCommGroup V] [Module K V]

theorem dense_away_level_fixed (f : Γ →* G × H) (hf : DenseRange f)
    (hsurj : Function.Surjective (fun γ => (f γ).2))
    (hperfect : commutator G = ⊤) (L : OpenSubgroup H)
    (ρ : H →* (V ≃ₗ[K] V)) (v : V) (hv : v ≠ 0)
    (hline : ∀ a ∈ L, ∃ c : Kˣ, ρ a v = (c : K) • v)
    (U : OpenSubgroup G)
    (hfixed : ∀ γ, (f γ).2 ∈ L → (f γ).1 ∈ U → ρ (f γ).2 v = v) :
    ∀ a ∈ L, ρ a v = v := by
  let r : DenseOpenRestriction.TestTransport.openSecondFactor f L →* (V ≃ₗ[K] V) :=
    ρ.comp (((MonoidHom.snd G H).comp f).comp (DenseOpenRestriction.TestTransport.openSecondFactor f L).subtype)
  have hr : ∀ γ : DenseOpenRestriction.TestTransport.openSecondFactor f L, r γ v = v :=
    EigenlineCharacter.TestTransport.dense_invariant_line_fixed r v hv
      (fun γ => hline (f γ.val).2 γ.property)
      (DenseOpenRestriction.TestTransport.restrictedFirstFactor f L) (DenseOpenRestriction.TestTransport.restrictedFirstFactor_dense f L hf) hperfect U
      (fun γ hγ => hfixed γ.val γ.property hγ)
  intro a ha
  obtain ⟨γ, hγ⟩ := hsurj a
  change (f γ).2 = a at hγ
  have hmem : γ ∈ DenseOpenRestriction.TestTransport.openSecondFactor f L := by
    change (f γ).2 ∈ L
    rw [hγ]
    exact ha
  have h := hr ⟨γ, hmem⟩
  change ρ (f γ).2 v = v at h
  rwa [hγ] at h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseAwayFixed.TestTransport
