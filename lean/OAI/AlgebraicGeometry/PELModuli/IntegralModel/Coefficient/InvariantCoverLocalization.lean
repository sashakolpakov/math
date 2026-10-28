import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GenericOpenEquality

/-! # Invariant Cover Localization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.InvariantCoverLocalization.Coefficients

noncomputable section

section

/-! Equality of generic opens becomes equality on every test point
away from one nonzero coefficient of the actual model base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem coefficient_open_equality_away {X : Over (Spec (.of K))}
    (M : Models.Coefficients.CoefficientModel R K X) [IsNoetherian M.model.left] (U V : M.model.left.Opens)
    (h : M.specialization ⁻¹ᵁ U = M.specialization ⁻¹ᵁ V) :
    ∃ r : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K M.coefficients, r ≠ 0 ∧
      ∀ x : M.model.left, r ∉ (M.model.hom x).asIdeal → (x ∈ U ↔ x ∈ V) :=
  GenericOpenEqualityLocalization.generic_open_equality_away_of_field_baseChange
    (algebraMap (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K M.coefficients) K) Subtype.val_injective M.model.hom U V
    (GenericOpenEquality.Coefficients.generic_open_equality_of_specialization M U V h)

end

/-! A finite generic cover and all its finitely many invariance
equations hold uniformly after one coefficient localization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem finite_invariant_cover_away {I G : Type} [Finite I] [Finite G]
    {X : Over (Spec (.of K))} (M : Models.Coefficients.CoefficientModel R K X) [IsNoetherian M.model.left]
    (V : I → M.model.left.Opens) (a : G → (M.model ⟶ M.model)) (b : G → (X ⟶ X))
    (hcomp : ∀ g, M.specialization ≫ (a g).left = (b g).left ≫ M.specialization)
    (hcover : (⨆ i, M.specialization ⁻¹ᵁ V i) = ⊤)
    (hInv : ∀ g i, (b g).left ⁻¹ᵁ (M.specialization ⁻¹ᵁ V i) = M.specialization ⁻¹ᵁ V i) :
    ∃ r : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K M.coefficients, r ≠ 0 ∧
      (∀ x : M.model.left, r ∉ (M.model.hom x).asIdeal → ∃ i, x ∈ V i) ∧
      (∀ g i (x : M.model.left), r ∉ (M.model.hom x).asIdeal → ((a g).left x ∈ V i ↔ x ∈ V i)) := by
  classical
  let : Fintype (G × I) := Fintype.ofFinite (G × I)
  have htop : M.specialization ⁻¹ᵁ iSup V = M.specialization ⁻¹ᵁ ⊤ := by
    ext x
    change M.specialization x ∈ iSup V ↔ M.specialization x ∈ (⊤ : M.model.left.Opens)
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hx : x ∈ ⨆ i, M.specialization ⁻¹ᵁ V i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  obtain ⟨r₀, hr₀, hcov⟩ := coefficient_open_equality_away M (iSup V) ⊤ htop
  have hEq (j : G × I) : M.specialization ⁻¹ᵁ ((a j.1).left ⁻¹ᵁ V j.2) =
      M.specialization ⁻¹ᵁ V j.2 := by
    rw [← Scheme.Hom.comp_preimage, hcomp, Scheme.Hom.comp_preimage]
    exact hInv j.1 j.2
  choose r hr hgood using fun j : G × I =>
    coefficient_open_equality_away M ((a j.1).left ⁻¹ᵁ V j.2) (V j.2) (hEq j)
  let d := ∏ j : G × I, r j
  refine ⟨r₀ * d, mul_ne_zero hr₀ (Finset.prod_ne_zero_iff.mpr (fun j _ => hr j)), ?_, ?_⟩
  · intro x hx
    exact Opens.mem_iSup.mp ((hcov x (fun h => hx ((M.model.hom x).asIdeal.mul_mem_right d h))).mpr trivial)
  · intro g i x hx
    apply hgood (g, i) x
    intro h
    have hd : r (g, i) ∣ r₀ * d :=
      (Finset.dvd_prod_of_mem r (Finset.mem_univ (g, i))).trans (dvd_mul_left d r₀)
    exact hx ((M.model.hom x).asIdeal.mem_of_dvd hd h)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.InvariantCoverLocalization.Coefficients
