import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.ScalarComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal

/-! # Power Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.PowerMap.FreeRelativePowerMap

noncomputable section

/-! # Power-coordinate maps on the actual relative free PD resolution -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ : Type u) [CommRing R] (I : Ideal R) (δ : DividedPowers I)

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ

def total (a : σ → R) (i : σ) : G := algebraMap R G (a i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i

variable (m : ℕ) (a c : σ → R) (h : ∀ i, a i ^ m - c i ∈ I)

def image (i : σ) : G := total R σ a i ^ m - algebraMap R G (c i)

include h in
theorem image_mem (i : σ) : image R σ m a c i ∈ IG := by
  let q := Ideal.Quotient.mk IG
  have hg : q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i 1 one_ne_zero)
  have hc : q (algebraMap R G (a i ^ m - c i)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Or.inl ⟨⟨a i ^ m - c i, h i⟩, rfl⟩))
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (total R σ a i ^ m - algebraMap R G (c i)) = 0
  simp only [total, map_sub, map_pow, map_add, hg, add_zero]
  simpa only [map_sub, map_pow] using hc

def map : G →ₐ[R] G := Universal.FreeRelativeUniversal.lift R σ G IG γ
  (image R σ m a c) (image_mem R σ I m a c h)

theorem map_isDPMorphism : DividedPowers.IsDPMorphism γ γ (map R σ I δ m a c h).toRingHom :=
  Universal.FreeRelativeUniversal.lift_isDPMorphism R σ I δ G IG γ
    (Powers.FreeRelativePowers.base_isDPMorphism R σ I δ)
    (image R σ m a c) (image_mem R σ I m a c h)

theorem map_coordinate (i : σ) :
    map R σ I δ m a c h (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = image R σ m a c i :=
  Universal.FreeRelativeUniversal.lift_coordinate R σ G IG γ
    (image R σ m a c) (image_mem R σ I m a c h) i

theorem map_total (i : σ) : map R σ I δ m a c h (total R σ c i) = total R σ a i ^ m := by
  rw [total, _root_.map_add, AlgHom.commutes, map_coordinate, image]
  abel

def relativeComplexMap : PD.DeRham.PDDeRham.complex R G IG γ ⟶ PD.DeRham.PDDeRham.complex R G IG γ :=
  PD.DeRhamEquivalence.PDDeRhamEquivalence.complexMap (A := CommAlgCat.of R G) (B := CommAlgCat.of R G)
    (CommAlgCat.ofHom (map R σ I δ m a c h)) (map_isDPMorphism R σ I δ m a c h)

theorem relativeComplexMap_symbol (n : ℕ) (b : G) (v : Fin n → σ) :
    ((relativeComplexMap R σ I δ m a c h).f n).hom
      (PD.DeRham.PDDeRham.symbol R G IG γ b (total R σ c ∘ v)) =
        PD.DeRham.PDDeRham.symbol R G IG γ (map R σ I δ m a c h b)
          (fun j => total R σ a (v j) ^ m) := by
  have hs := PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol (A := CommAlgCat.of R G) (B := CommAlgCat.of R G)
    (CommAlgCat.ofHom (map R σ I δ m a c h)) (map_isDPMorphism R σ I δ m a c h)
    n b (total R σ c ∘ v)
  change ((relativeComplexMap R σ I δ m a c h).f n).hom _ =
    PD.DeRham.PDDeRham.symbol R G IG γ (map R σ I δ m a c h b)
      (fun j => map R σ I δ m a c h (total R σ c (v j))) at hs
  simpa only [map_total] using hs

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.PowerMap.FreeRelativePowerMap
