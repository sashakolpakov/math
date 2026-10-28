import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.CartanAutomorphism
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # Killing -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.Killing.Construction

noncomputable section

section

/-! A symmetric positive definite real bilinear form admits
continuous coordinates in which it is the Euclidean inner product. -/

open scoped Classical

theorem bilinear_eval_orthogonal_basis
    {L ι : Type*} [AddCommGroup L] [Module ℝ L] [Fintype ι]
    (F : LinearMap.BilinForm ℝ L) (b : Module.Basis ι ℝ L) (hb : F.IsOrthoᵢ b) (x y : L) :
    F x y = ∑ i, b.equivFun x i * b.equivFun y i * F (b i) (b i) := by
  classical
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [Module.Basis.equivFun_apply]
    ring
  · intro j _ hij
    rw [show F (b j) (b i) = 0 from hb hij]
    simp
  · simp

theorem positive_bilinear_euclidean_coordinates
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    (F : LinearMap.BilinForm ℝ L) (hF : LinearMap.IsSymm F) (hpos : ∀ x : L, x ≠ 0 → 0 < F x x) :
    ∃ Φ : L ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ L)),
      ∀ x y : L, inner ℝ (Φ x) (Φ y) = F x y := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hF
  let c : Fin (Module.finrank ℝ L) → ℝ := fun i => Real.sqrt (F (b i) (b i))
  have hc (i : Fin (Module.finrank ℝ L)) : 0 < c i := Real.sqrt_pos.mpr (hpos (b i) (b.ne_zero i))
  let d := LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfNeZero ℝ ℝ (c i) (ne_of_gt (hc i))
  let e := b.equivFun.trans d
  let Φ : L ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ L)) :=
    (e.trans (WithLp.linearEquiv 2 ℝ (Fin (Module.finrank ℝ L) → ℝ)).symm).toContinuousLinearEquiv
  have hΦ (x : L) (i : Fin (Module.finrank ℝ L)) : Φ x i = c i * b.equivFun x i := rfl
  refine ⟨Φ, fun x y => ?_⟩
  change (∑ i, Φ y i * Φ x i) = F x y
  rw [bilinear_eval_orthogonal_basis F b hb]
  apply Finset.sum_congr rfl
  intro i _
  rw [hΦ, hΦ]
  have hci : c i ^ 2 = F (b i) (b i) := Real.sq_sqrt (le_of_lt (hpos (b i) (b.ne_zero i)))
  calc
    (c i * b.equivFun y i) * (c i * b.equivFun x i) =
        c i ^ 2 * (b.equivFun x i * b.equivFun y i) := by ring
    _ = _ := by rw [hci]; ring

end

section

/-! The automorphism group of a real Killing bracket has Euclidean
coordinates in which it is closed under taking operator adjoints. -/

open _root_.ContinuousLinearMap

theorem formCoordinates_adjoint
    {L V : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (F : LinearMap.BilinForm ℝ L) (Φ : L ≃L[ℝ] V)
    (hΦ : ∀ x y, inner ℝ (Φ x) (Φ y) = F x y)
    (g h : L →L[ℝ] L) (hgh : ∀ x y, F (g x) y = F x (h y)) :
    adjoint (Φ.conjContinuousAlgEquiv g) = Φ.conjContinuousAlgEquiv h := by
  have he : Φ.conjContinuousAlgEquiv g = adjoint (Φ.conjContinuousAlgEquiv h) := by
    apply (eq_adjoint_iff _ _).mpr
    intro v w
    obtain ⟨x, rfl⟩ := Φ.surjective v
    obtain ⟨y, rfl⟩ := Φ.surjective w
    simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
      ContinuousLinearEquiv.symm_apply_apply]
    rw [hΦ, hΦ]
    exact hgh x y
  simpa only [adjoint_adjoint] using congrArg adjoint he

theorem exists_killing_automorphism_selfAdjoint_coordinates
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ Φ : L ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ L)),
      ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
        ∃ h : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange h B = B ∧
          adjoint (Φ.conjContinuousAlgEquiv g.toContinuousLinearMap) =
            Φ.conjContinuousAlgEquiv h.toContinuousLinearMap := by
  obtain ⟨θ, hθ, hθB, hpos⟩ := Bracket.CartanAutomorphism.Construction.exists_killing_bracket_cartan_involution B hB hK
  let F := Bracket.CartanAutomorphism.Construction.cartanTwistForm B θ.toContinuousLinearMap
  have hF : LinearMap.IsSymm F := (LinearMap.BilinForm.isSymm_iff).mp
    ⟨Bracket.CartanAutomorphism.Construction.cartanTwistForm_symmetric_of_involution B θ hθ hθB⟩
  have hp : ∀ x : L, x ≠ 0 → 0 < F x x := by
    intro x hx
    exact hpos x hx
  obtain ⟨Φ, hΦ⟩ := positive_bilinear_euclidean_coordinates F hF hp
  refine ⟨Φ, fun g hg => ⟨Bracket.CartanAutomorphism.Construction.cartanAutomorphismAdjoint θ g,
    Bracket.CartanAutomorphism.Construction.cartanAutomorphismAdjoint_preserves B θ g hθB hg, ?_⟩⟩
  exact formCoordinates_adjoint F Φ hΦ g.toContinuousLinearMap
    (Bracket.CartanAutomorphism.Construction.cartanAutomorphismAdjoint θ g).toContinuousLinearMap
    (Bracket.CartanAutomorphism.Construction.cartanTwistForm_automorphism_adjoint B θ g hθ hg)

end

/-! Transporting brackets between distinct finite-dimensional normed
spaces preserves Lie brackets and nondegeneracy of the Killing form. -/

variable {L V : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def continuousBracketTransport (e : L ≃L[ℝ] V) (B : L →L[ℝ] L →L[ℝ] L) :
    V →L[ℝ] V →L[ℝ] V :=
  (ContinuousLinearMap.compL ℝ V L V e.toContinuousLinearMap).comp
    (((B.comp e.symm.toContinuousLinearMap).flip.comp e.symm.toContinuousLinearMap).flip)

theorem continuousBracketTransport_apply (e : L ≃L[ℝ] V) (B : L →L[ℝ] L →L[ℝ] L) (x y : V) :
    continuousBracketTransport e B x y = e (B (e.symm x) (e.symm y)) := rfl

theorem continuousBracketTransport_inverse (e : L ≃L[ℝ] V) (B : L →L[ℝ] L →L[ℝ] L) :
    continuousBracketTransport e.symm (continuousBracketTransport e B) = B := by
  ext x y
  simp only [continuousBracketTransport_apply, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.symm_apply_apply]

theorem continuousBracketTransport_injective (e : L ≃L[ℝ] V) :
    Function.Injective (continuousBracketTransport e) := by
  intro B C h
  have he := congrArg (continuousBracketTransport e.symm) h
  simpa only [continuousBracketTransport_inverse] using he

theorem continuousBracketTransport_change (e : L ≃L[ℝ] V)
    (g : L ≃L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L) :
    continuousBracketTransport e (ContinuousBracketChange.Construction.continuousBracketChange g B) =
      ContinuousBracketChange.Construction.continuousBracketChange ((e.symm.trans g).trans e) (continuousBracketTransport e B) := by
  ext x y
  simp only [continuousBracketTransport_apply, ContinuousBracketChange.Construction.continuousBracketChange_apply,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.symm_apply_apply]

theorem continuousBracketTransport_isLie [FiniteDimensional ℝ L] [FiniteDimensional ℝ V]
    (e : L ≃L[ℝ] V) (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) :
    ContinuousBracketConstraints.Construction.IsContinuousLieBracket (continuousBracketTransport e B) := by
  constructor
  · intro x
    rw [continuousBracketTransport_apply, hB.1, map_zero]
  · apply (ContinuousJacobi.Construction.continuousJacobi_zero_iff _).mpr
    intro x y z
    simp only [continuousBracketTransport_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [(ContinuousJacobi.Construction.continuousJacobi_zero_iff B).mp hB.2, map_add]

theorem continuousBracketTransport_killing [FiniteDimensional ℝ L] [FiniteDimensional ℝ V]
    (e : L ≃L[ℝ] V) (B : L →L[ℝ] L →L[ℝ] L) (x y : V) :
    ContinuousInnerDerivations.Construction.continuousBracketKillingForm (continuousBracketTransport e B) x y =
      ContinuousInnerDerivations.Construction.continuousBracketKillingForm B (e.symm x) (e.symm y) := by
  have he (z : V) : (continuousBracketTransport e B z).toLinearMap =
      e.toLinearEquiv.conjAlgEquiv ℝ ((B (e.symm z)).toLinearMap) := by ext w; rfl
  rw [ContinuousInnerDerivations.Construction.continuousBracketKillingForm_apply, he, he, ← map_mul, LinearMap.trace_map]
  rfl

theorem continuousBracketTransport_killing_nondegenerate
    [FiniteDimensional ℝ L] [FiniteDimensional ℝ V]
    (e : L ≃L[ℝ] V) (B : L →L[ℝ] L →L[ℝ] L)
    (hB : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    (ContinuousInnerDerivations.Construction.continuousBracketKillingForm (continuousBracketTransport e B)).Nondegenerate := by
  constructor
  · intro x hx
    have hz : e.symm x = 0 := hB.1 (e.symm x) (fun y => by
      have h := hx (e y)
      simpa only [continuousBracketTransport_killing, ContinuousLinearEquiv.symm_apply_apply] using h)
    apply e.symm.injective
    simpa only [map_zero] using hz
  · intro x hx
    have hz : e.symm x = 0 := hB.2 (e.symm x) (fun y => by
      have h := hx (e y)
      simpa only [continuousBracketTransport_killing, ContinuousLinearEquiv.symm_apply_apply] using h)
    apply e.symm.injective
    simpa only [map_zero] using hz

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.Killing.Construction
