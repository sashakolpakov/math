import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RefinementFromAuxiliaryModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallProjectiveComponents
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DegreeTwoExclusion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveBaseChange

/-! # Components From Auxiliary Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentsFromAuxiliaryModel

noncomputable section

/-! The actual auxiliary pure fine model supplies ReferenceFamily's original
projective components and principal special-unitary quotient, through
the existing arithmetic refinement and native complex comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem moduli_components_from_auxiliaryModel
    {E : Type} [Field E] [NumberField E] [aE : Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K]
    (iota : E →+* K) (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    {L : ℕ} (A : Pure.Fine.PurePolarizedModel (3 * s) P.polarizationType L (Spec (.of K)))
    (hA : A.IsFine) (hL : 3 ≤ L) (QA : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation A.space)
    (Kaux : OpenSubgroup P.FiniteSpecialUnitary) (M : ℕ) (hM : 0 < M) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ M ∣ N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N →
      (∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g →
        LinearMap.det g.toLinearMap = 1) ∧
      P.adelicPrincipalLevel N ≤ Kaux.toSubgroup ∧
      ∃ Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E),
        (∀ g, g ∈ Γ ↔ NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g ∧ LinearMap.det g.toLinearMap = 1) ∧
        (∀ g ∈ Γ, ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
        ∃ S : Models.FinePELModel P iota N,
          S.IsFine ∧ S.HasProjectiveBallComponents κ ∧
          ∃ (C : S.ComplexComponent κ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety),
            S.IsProjectiveComponent κ C X ∧ P.IsUniformizedBy X Γ := by
  have hcanonical : aE = (DivisionRing.toRatAlgebra : Algebra ℚ E) := Subsingleton.elim _ _
  subst aE
  have hs : 1 < s := P.one_lt_of_admissible hP hdegree
  have hs0 : 0 < s := lt_trans Nat.zero_lt_one hs
  obtain ⟨N₀, h3, hMdiv, hdeep⟩ :=
    RefinementFromAuxiliaryModel.exists_quasiProjective_fine_arithmetic_level_refinement_from_auxiliaryModel
      P iota hP A hA hL QA Kaux M hM
  refine ⟨N₀, h3, hMdiv, ?_⟩
  intro N hN hdiv
  obtain ⟨hdet, haux, Γ, hΓ, hfree, S, hS, ⟨Q⟩⟩ := hdeep N hN hdiv
  have hN3 : 3 ≤ N := h3.trans (Nat.le_of_dvd hN hdiv)
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let : LocallyOfFiniteType S.space.hom := Q.locallyFiniteType
  let : QuasiCompact S.space.hom := Q.quasiCompact
  let Qc : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation (S.complexFiber κ) :=
    Q.baseChange (Spec.map (CommRingCat.ofHom κ))
  have hΓeq : Γ = Groups.principalSpecialUnitary P.b P.lattice N := by
    apply Subgroup.ext
    intro g
    exact (hΓ g).trans (Groups.mem_principalSpecialUnitary P.b P.lattice N g).symm
  subst Γ
  refine ⟨hdet, haux, Groups.principalSpecialUnitary P.b P.lattice N, hΓ, hfree, S, hS, ?_, ?_⟩
  · exact S.hasProjectiveBallComponents_of_one_lt hS κ hP hκ Qc hN3 hs hdegree
  · exact S.exists_principal_projective_component hS κ hP hκ Qc hN3 hs0 hdegree

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentsFromAuxiliaryModel
