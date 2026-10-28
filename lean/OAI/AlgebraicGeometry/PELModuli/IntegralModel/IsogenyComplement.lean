import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CountableParameters
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyFactorizationIs
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothComponents
import Mathlib.GroupTheory.OrderOfElement

/-! # Isogeny Complement -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyComplement

noncomputable section

/-! A finite étale kernel over an algebraically closed field is killed by
the cardinality of its actual group of rational points. Reducedness upgrades
the point calculation to a scheme identity on every test scheme. The proved
fpqc quotient theorem then constructs a complementary group morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem finite_parameterPoints (H : Over (Spec (.of k))) [IsFinite H.hom] :
    Finite (CountableParameters.ParameterPoints H) := by
  have h := H.hom.finite_preimage (Set.toFinite (Set.univ : Set (Spec (.of k))))
  simp only [Set.preimage_univ] at h
  have : Finite H.left := Set.finite_univ_iff.mp h
  exact Finite.of_equiv _ (CountableParameters.parameterPointClosedEquiv H).symm

/-- A finite reduced group scheme is annihilated scheme-theoretically by
one positive integer, with no kernel-exponent premise. -/
theorem finite_reduced_group_annihilated
    (H : Over (Spec (.of k))) [GrpObj H] [IsFinite H.hom] [IsReduced H.left] :
    ∃ n : ℕ, 0 < n ∧ (𝟙 H : H ⟶ H) ^ n = 1 ∧
      ∀ (T : Over (Spec (.of k))) (x : T ⟶ H), x ^ n = 1 := by
  have : Finite (CountableParameters.ParameterPoints H) := finite_parameterPoints H
  let n := Nat.card (CountableParameters.ParameterPoints H)
  have hn : 0 < n := Nat.card_pos
  have hpow : (𝟙 H : H ⟶ H) ^ n = 1 := by
    apply Albanese.Construction.ClosedPoints.hom_ext_of_points H H
    intro p
    rw [MonObj.comp_pow, Category.comp_id, MonObj.comp_one]
    exact pow_card_eq_one'
  refine ⟨n, hn, hpow, ?_⟩
  intro T x
  have h := congrArg (fun f : H ⟶ H => x ≫ f) hpow
  simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using h

variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]

/-- Finite étaleness supplies reducedness of the actual kernel. Its finite
point group therefore gives a bound valid on all, including nonreduced,
test schemes. -/
theorem finite_etale_kernel_annihilated
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Etale f.left] :
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Spec (.of k))) (x : T ⟶ A),
      x ≫ f = 1 → x ^ n = 1 := by
  let H := Picard.PoincareBundle.Kernel.Scheme.kernelObject f
  let : GrpObj H := Picard.PoincareBundle.Kernel.Scheme.kernelGroup f
  have : IsFinite H.hom := Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite f
  have : Etale H.hom := by
    change Etale (Picard.PoincareBundle.Kernel.Scheme.kernelObject f).hom
    rw [Picard.PoincareBundle.Kernel.Scheme.kernel_hom_eq_snd f]
    exact MorphismProperty.of_isPullback (P := @Etale)
      (Picard.PoincareBundle.Kernel.Scheme.kernel_isPullback f) inferInstance
  have : IsReduced H.left := ArithmeticGeometry.Models.SpreadingOut.SmoothComponents.Construction.smooth_scheme_reduced H.hom
  obtain ⟨n, hn, _, hpow⟩ := finite_reduced_group_annihilated H
  refine ⟨n, hn, ?_⟩
  intro T x hx
  let z : T ⟶ H := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv f T).symm ⟨x, hx⟩
  have hz : z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = x := pullback.lift_fst _ _ _
  rw [← hz, ← MonObj.pow_comp, hpow T z, MonObj.one_comp]

variable [IsCommMonObj A] [IsCommMonObj B]

/-- Construct a reverse isogeny map and both multiplication identities
from finite étale surjectivity alone. -/
theorem exists_complementary_map_of_finite_etale
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Etale f.left] [Surjective f.left] :
    ∃ (n : ℕ) (d : B ⟶ A), 0 < n ∧ IsMonHom d ∧
      f ≫ d = (𝟙 A : A ⟶ A) ^ n ∧ d ≫ f = (𝟙 B : B ⟶ B) ^ n ∧
      ∀ (T : Over (Spec (.of k))) (x : T ⟶ B), x ≫ d = 1 → x ^ n = 1 := by
  obtain ⟨n, hn, hker⟩ := finite_etale_kernel_annihilated f
  obtain ⟨d, ⟨hd, hfd⟩, _⟩ := IsogenyFactorizationIs.IsogenyFactorization.fpqc_multiple_descent f (𝟙 A) n hker
  have : EffectiveEpi f := IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc f
  have hdf : d ≫ f = (𝟙 B : B ⟶ B) ^ n := by
    apply (cancel_epi f).mp
    rw [← Category.assoc, hfd, MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, Category.comp_id]
  refine ⟨n, d, hn, hd, hfd, hdf, ?_⟩
  intro T x hx
  have h := congrArg (fun g : B ⟶ B => x ≫ g) hdf
  have : IsMonHom d := hd
  simpa only [← Category.assoc, hx, MonObj.one_comp, MonObj.comp_pow,
    Category.comp_id] using h.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyComplement
