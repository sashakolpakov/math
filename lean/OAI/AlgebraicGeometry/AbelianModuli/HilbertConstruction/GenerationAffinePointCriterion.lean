import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GenerationLocus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RangeCriterion

/-! # Generation Affine Point Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenerationAffinePointCriterion

noncomputable section

/-! Arbitrary affine parameter maps land in the global generation open exactly when their actual quotient relations are generated. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ α : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ] [Fintype α]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq α]
variable {S : Scheme.{u}} {M : Over S}
variable (q : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
variable (k : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S)
variable (F : α → Matrix μ ν Γ(M.left, ⊤)) (hF : ∀ t, Grassmann.IncidenceCondition.GrassmannIncidenceCondition q k (F t) (𝟙 M))

theorem grassmannGenerationOpen_affine_point_iff (R : CommRingCat.{u}) (f : Spec R ⟶ S)
    (x : Over.mk f ⟶ M)
    (N : Module.Grassmannian R (ν → R) (Fintype.card ι))
    (K : Module.Grassmannian R (μ → R) (Fintype.card κ))
    (hN : x ≫ q = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
    (hK : x ≫ k = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K)
    (F₀ : α → Matrix μ ν R)
    (hFF : ∀ t, (F t).map x.left.appTop.hom = (F₀ t).map (Scheme.ΓSpecIso R).inv.hom) :
    Set.range x.left ⊆ (Grassmann.GenerationOpen.grassmannGenerationOpen q k F hF : Set M.left) ↔
      K.toSubmodule = ⨆ t, N.toSubmodule.map (Matrix.toLin' (F₀ t)) := by
  have h₀ : ∀ t, Grassmann.IncidenceCondition.GrassmannIncidenceCondition (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K) ((F₀ t).map (Scheme.ΓSpecIso R).inv.hom) (𝟙 (Over.mk f)) := by
    intro t
    have ht := Grassmann.GenerationBaseChange.grassmannIncidence_identity_baseChange (F t) (hF t) x
    rw [hN, hK, hFF t] at ht
    exact ht
  have he : x.left ⁻¹ᵁ Grassmann.GenerationOpen.grassmannGenerationOpen q k F hF =
      Grassmann.GenerationOpen.grassmannGenerationOpen (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
        (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K) (fun t => (F₀ t).map (Scheme.ΓSpecIso R).inv.hom) h₀ :=
    (Grassmann.GenerationOpen.grassmannGenerationOpen_baseChange F hF x).trans
      (Affine.GenerationBaseChange.grassmannGenerationOpen_congr hN hK (funext hFF) _ h₀)
  rw [Open.RangeCriterion.range_subset_open_iff_preimage_eq_top, he]
  exact Affine.GenerationLocus.grassmannGenerationOpen_affine_iff R f N K F₀ h₀

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenerationAffinePointCriterion
