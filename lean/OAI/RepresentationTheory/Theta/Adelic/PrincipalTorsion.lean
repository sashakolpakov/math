import OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup
import OAI.RepresentationTheory.Theta.Adelic.CoefficientOrderFinite
import OAI.RepresentationTheory.Theta.Adelic.FiniteRingTorsion

/-! # Principal Torsion -/

namespace OAI.RepresentationTheory.Theta.Adelic.PrincipalTorsion

noncomputable section

/-! Genuine coefficient principal levels divisible by three times a
quadratic denominator contain no nonidentity finite-order elements. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.PrincipalCoefficientOrder OAI.RepresentationTheory.Theta.Adelic.CoefficientOrderFinite OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup
open OAI.RepresentationTheory.Theta.Adelic.FiniteRingTorsion

variable (F : Type) [Field F] [NumberField F] (d : F)
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

theorem principalLevel_torsion_free (t : ℕ) (q : 𝓞 F) (hq : (q : F) = (t : F) * d)
    (N : ℕ) (hN : 3 * t ∣ N) (g : SpecialUnitary.SU H.val) (hg : BallGeometryData.PrincipalLevel N g)
    (k : ℕ) (hk : 0 < k) (hp : g ^ k = 1) : g = 1 := by
  let O := PrincipalCoefficientOrder.coefficientOrder F d t q hq
  let : Module.Finite ℤ O := CoefficientOrderFinite.coefficientOrder_finite F d t q hq
  let : Module.IsTorsionFree ℤ O := CoefficientOrderFinite.coefficientOrder_torsionFree F d t q hq
  have hcong : ∀ i j, ∃ b : O,
      (PrincipalSubgroup.suSpecialLinear H.val g).val i j - (1 : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) i j =
        3 • (b : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) := by
    intro i j
    obtain ⟨a, b, hab⟩ := hg i j
    obtain ⟨l, hl⟩ := hN
    let x : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d := (t * l : ℕ) * (⟨(a : F), (b : F)⟩ : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)
    have hx : x ∈ O := by
      refine ⟨(t * l : ℕ) * a, l * b, ?_⟩
      apply QuadraticAlgebra.ext
      · simp [x]
      · simp [x, Nat.cast_mul, mul_assoc]
    refine ⟨⟨x, hx⟩, hab.trans ?_⟩
    rw [hl]
    change ((3 * t * l : ℕ) : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) *
      (⟨(a : F), (b : F)⟩ : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) = 3 • x
    simp only [x, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hs := FiniteRingTorsion.subring_principal_torsion O (PrincipalSubgroup.suSpecialLinear H.val g) 3 (by decide)
    hcong k hk (by rw [← map_pow, hp, map_one])
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val hs

end

end OAI.RepresentationTheory.Theta.Adelic.PrincipalTorsion
