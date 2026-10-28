import OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateSeparation
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Interpolation
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Arithmetic

/-! # Split Coordinates -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.SplitCoordinates

noncomputable section

/-! The actual embedding-labelled coordinate maps are surjective modulo
every q-power and have exactly the stated principal kernels. -/

open _root_.NumberField _root_.Polynomial

theorem exists_split_coordinates_bound
    (E : Type) [Field E] [NumberField E] [aE : Algebra ℚ E] [IsGalois ℚ E] :
    ∃ d : ℕ, ∀ (K : Type) [Field K] [NumberField K]
      (κ : K →+* ℂ) (iota : E →+* K)
      (q : ℕ) [Fact q.Prime] (j : Arithmetic.QadicChoice K κ q),
      d < q → j.HasSplitCoordinates iota := by
  have hA : aE = (DivisionRing.toRatAlgebra : Algebra ℚ E) := Subsingleton.elim _ _
  subst aE
  obtain ⟨B, hint⟩ := NumberTheory.Splitting.Integral.SplitPrimesConstruction.exists_integral_powerBasis E
  let θ : RingOfIntegers E := ⟨B.gen, hint⟩
  let f := minpoly ℤ θ
  have hf : f.natDegree ≠ 0 := (minpoly.natDegree_pos θ.isIntegral).ne'
  have hsep : (f.map (Int.castRingHom ℚ)).Separable := by
    have h := Algebra.IsSeparable.isSeparable ℚ B.gen
    change (minpoly ℚ (algebraMap (RingOfIntegers E) E θ)).Separable at h
    rw [minpoly.isIntegrallyClosed_eq_field_fractions ℚ E θ.isIntegral] at h
    exact h
  obtain ⟨d, hd, hgood⟩ := NumberTheory.Splitting.Polynomial.SplitPrimesConstruction.exists_separability_denominator f hf hsep
  refine ⟨d.natAbs, fun K _ _ κ iota q _ j hq => ?_⟩
  have hsepq : (f.map (Int.castRingHom (ZMod q))).Separable := by
    apply hgood q (Fact.out : q.Prime)
    intro hdiv
    have hn : q ∣ d.natAbs := by exact_mod_cast Int.natAbs_dvd_natAbs.mpr hdiv
    exact (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hd) hq) hn
  let r := j.residue.comp (RingOfIntegers.mapRingHom iota)
  have hinj : Function.Injective (fun τ : Gal(E/ℚ) =>
      PadicInt.toZMod (j.localCharacter iota τ θ)) :=
    CoordinateSeparation.residue_characters_injective_at_generator B hint r hsepq
  intro n
  have hs : Function.Surjective (j.residueCoordinates iota n) :=
    Interpolation.characters_surjective_mod_pow (j.localCharacter iota) θ hinj n
  refine ⟨hs, ?_⟩
  have hk := Arithmetic.coordinate_kernel_of_surjective (q ^ n)
    (pow_ne_zero n (Fact.out : q.Prime).ne_zero) (j.residueCoordinates iota n) hs
  simpa only [Nat.cast_pow] using hk

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.SplitCoordinates
