import OAI.AlgebraicGeometry.PELModuli.CMPoints.RealizedIsogenies
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Products

/-! # Common Hodge Multipliers -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CommonHodgeMultipliers

noncomputable section

section

/-! Finitely many rational Hodge maps are realized with one common
positive integer multiplier, by actual algebraic group homomorphisms. -/

open _root_.CategoryTheory
open scoped Classical _root_.CategoryTheory.MonObj

theorem exists_realized_algebraic_maps_common_multiplier
    {I U V : Type*} [Fintype I] [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V]
    {H : I → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} {J : I → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V}
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (H i)) (S : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (J i))
    (f : I → U →ₗ[ℚ] V) (hf : ∀ i, ComplexMultiplication.WeightOne.CM.IsHodgeMap (H i) (J i) (f i)) :
    ∃ d : ℕ, 0 < d ∧
      ∃ g : ∀ i, (S i).abelianVariety.toOver ⟶ (R i).abelianVariety.toOver,
        (∀ i, IsMonHom (g i)) ∧
        ∀ i, ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (g i) = (d : ℚ) • (R i).realizedMap (S i) (f i) := by
  classical
  have hex (i : I) := RealizedMaps.exists_realized_algebraic_map (R i) (S i) (f i) (hf i)
  choose n hn g hg hgn using hex
  let d := ∏ i, n i
  let k (i : I) := ∏ j ∈ Finset.univ.erase i, n j
  have hd : 0 < d := Finset.prod_pos (fun i _ => hn i)
  have hk (i : I) : k i * n i = d := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  refine ⟨d, hd, fun i => g i ≫ AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism (R i).abelianVariety (k i), ?_, ?_⟩
  · intro i
    let : IsMonHom (g i) := hg i
    let : IsMonHom (AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism (R i).abelianVariety (k i)) := RealizedIsogenies.abelianPower_isMonHom _ _
    infer_instance
  · intro i
    rw [RealizedIsogenies.abelianH1Pullback_comp, RealizedIsogenies.abelianH1Pullback_power, hgn i]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul, smul_smul]
    rw [← Nat.cast_mul, hk i]

end

/-! The actual inclusions and projections of a finite CM Hodge product
are Hodge maps, hence yield algebraic maps with common multipliers. -/

open _root_.CategoryTheory
open scoped Classical TensorProduct

variable {I V : Type*} [Fintype I] [AddCommGroup V] [Module ℚ V]

theorem hodgePiCoordinates_eval (i : I) (x : ComplexMultiplication.WeightOne.CM.Complexification (I → V)) :
    (LinearMap.proj i : (I → V) →ₗ[ℚ] V).baseChange ℂ x = Products.hodgePiCoordinates x i := by
  induction x using TensorProduct.inductionOn with
  | tmul z v => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem hodgePi_proj_isHodgeMap (H : I → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V) (i : I) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (Products.hodgePi H) (H i) (LinearMap.proj i) := by
  intro x hx
  rw [hodgePiCoordinates_eval]
  exact hx i

theorem exists_hodgePi_algebraic_factor_maps
    (H : I → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V) (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (Products.hodgePi H))
    (S : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (H i)) :
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
      ∃ (f : ∀ i, R.abelianVariety.toOver ⟶ (S i).abelianVariety.toOver)
        (g : ∀ i, (S i).abelianVariety.toOver ⟶ R.abelianVariety.toOver),
        (∀ i, IsMonHom (f i)) ∧ (∀ i, IsMonHom (g i)) ∧
        (∀ i, ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (f i) =
          (n : ℚ) • (S i).realizedMap R (LinearMap.single ℚ (fun _ : I => V) i)) ∧
        (∀ i, ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (g i) =
          (m : ℚ) • R.realizedMap (S i) (LinearMap.proj i)) := by
  obtain ⟨n, hn, f, hf, hfn⟩ := exists_realized_algebraic_maps_common_multiplier S (fun _ => R)
    (fun i => LinearMap.single ℚ (fun _ : I => V) i) (Products.hodgePi_single_isHodgeMap H)
  obtain ⟨m, hm, g, hg, hgm⟩ := exists_realized_algebraic_maps_common_multiplier (fun _ => R) S
    (fun i => LinearMap.proj i) (hodgePi_proj_isHodgeMap H)
  exact ⟨n, m, hn, hm, f, g, hf, hg, hfn, hgm⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CommonHodgeMultipliers
