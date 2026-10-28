import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.StabilizerLocalImage
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieLocalExponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.LinearIwasawaDecomposition

/-! # Triple Exponential Local Product -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.TripleExponentialLocalProduct.Construction

noncomputable section

/-! Three subspaces spanning the bracket derivations give a local
product of three exponential factors in the bracket automorphism group. -/

open scoped _root_.Topology
open NormedSpace Filter _root_.ContinuousLinearMap

theorem hasStrictFDerivAt_product_exp_three
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a b c : E →L[ℝ] A) :
    HasStrictFDerivAt (fun p => exp (a p) * exp (b p) * exp (c p)) (a + b + c) 0 := by
  have ha := Minkowski.LieLocalExponential.Construction.hasStrictFDerivAt_exp_linear_zero a
  have hb := Minkowski.LieLocalExponential.Construction.hasStrictFDerivAt_exp_linear_zero b
  have hc := Minkowski.LieLocalExponential.Construction.hasStrictFDerivAt_exp_linear_zero c
  convert! (ha.mul' hb).mul' hc using 1
  apply ContinuousLinearMap.ext
  intro p
  change a p + b p + c p = exp (a 0) * exp (b 0) * c p +
    (exp (a 0) * b p + a p * exp (b 0)) * exp (c 0)
  simp only [map_zero, exp_zero, one_mul, mul_one]
  abel

theorem bilinear_stabilizer_local_triple_exponential
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (U V W : Submodule ℝ (L →L[ℝ] L))
    (hU : U ≤ (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap.ker)
    (hV : V ≤ (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap.ker)
    (hW : W ≤ (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap.ker)
    (hsum : U ⊔ V ⊔ W = (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap.ker) :
    ∀ᶠ T in 𝓝 (1 : L →L[ℝ] L),
      (∀ x y, T (B x y) = B (T x) (T y)) →
      ∃ u ∈ U, ∃ v ∈ V, ∃ w ∈ W, exp u * exp v * exp w = T := by
  let : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
  let : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
  let : NormedRing (L →L[ℝ] L) := inferInstance
  let : NormedAlgebra ℝ (L →L[ℝ] L) := inferInstance
  let : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let E := U × (V × W)
  let : NormedAddCommGroup E := inferInstance
  let : NormedSpace ℝ E := inferInstance
  let : FiniteDimensional ℝ E := inferInstance
  let a₁ : E →L[ℝ] (L →L[ℝ] L) := U.subtypeL.comp (ContinuousLinearMap.fst ℝ U (V × W))
  let a₂ : E →L[ℝ] (L →L[ℝ] L) := V.subtypeL.comp
    ((ContinuousLinearMap.fst ℝ V W).comp (ContinuousLinearMap.snd ℝ U (V × W)))
  let a₃ : E →L[ℝ] (L →L[ℝ] L) := W.subtypeL.comp
    ((ContinuousLinearMap.snd ℝ V W).comp (ContinuousLinearMap.snd ℝ U (V × W)))
  let a := a₁ + a₂ + a₃
  let f : E → (L →L[ℝ] L) := fun p => exp (a₁ p) * exp (a₂ p) * exp (a₃ p)
  have ha : a.toLinearMap = U.subtype.coprod (V.subtype.coprod W.subtype) := by
    apply LinearMap.ext
    intro p
    change (p.1 : L →L[ℝ] L) + (p.2.1 : L →L[ℝ] L) + (p.2.2 : L →L[ℝ] L) =
      (p.1 : L →L[ℝ] L) + ((p.2.1 : L →L[ℝ] L) + (p.2.2 : L →L[ℝ] L))
    exact add_assoc _ _ _
  have hr : a.toLinearMap.range = (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap.ker := by
    rw [ha, LinearMap.range_coprod, LinearMap.range_coprod,
      Submodule.range_subtype, Submodule.range_subtype, Submodule.range_subtype, ← sup_assoc, hsum]
  have hd : HasStrictFDerivAt f a 0 :=
    hasStrictFDerivAt_product_exp_three (E := E) (A := L →L[ℝ] L) a₁ a₂ a₃
  have hi (p : E) : Function.Injective (f p) :=
    ((Bilinear.DerivationExponential.Construction.exp_continuousLinearMap_injective (a₁ p)).comp (Bilinear.DerivationExponential.Construction.exp_continuousLinearMap_injective (a₂ p))).comp
      (Bilinear.DerivationExponential.Construction.exp_continuousLinearMap_injective (a₃ p))
  have hp (p : E) (x y : L) : f p (B x y) = B (f p x) (f p y) := by
    have hd₁ := (OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B (a₁ p)).mp (hU p.1.property)
    have hd₂ := (OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B (a₂ p)).mp (hV p.2.1.property)
    have hd₃ := (OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B (a₃ p)).mp (hW p.2.2.property)
    change exp (a₁ p) (exp (a₂ p) (exp (a₃ p) (B x y))) = _
    rw [Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B (a₃ p) hd₃,
      Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B (a₂ p) hd₂, Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B (a₁ p) hd₁]
    rfl
  have hf0 : f 0 = 1 := by simp only [f, map_zero, exp_zero, mul_one]
  have h := Bilinear.StabilizerLocalImage.Construction.bilinear_stabilizer_local_image_of_range B f a hf0 hd hr hi hp
  filter_upwards [h] with T hT
  intro hTB
  obtain ⟨p, hp⟩ := hT hTB
  exact ⟨p.1.val, p.1.property, p.2.1.val, p.2.1.property, p.2.2.val, p.2.2.property, hp⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.TripleExponentialLocalProduct.Construction
