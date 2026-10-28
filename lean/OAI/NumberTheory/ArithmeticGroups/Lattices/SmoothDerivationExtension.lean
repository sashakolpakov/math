import Mathlib

/-! # Smooth Derivation Extension -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SmoothDerivationExtension.Construction

noncomputable section

/-! Derivations extend along formally smooth algebra extensions. The
proof lifts into the ring of dual numbers and extracts its infinitesimal
coordinate. -/

def derivationDualHom
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (D : Derivation k A B) : A →+* TrivSqZeroExt B B where
  toFun x := ⟨algebraMap A B x, D x⟩
  map_one' := TrivSqZeroExt.ext (map_one _) D.map_one_eq_zero
  map_zero' := TrivSqZeroExt.ext (map_zero _) (map_zero D)
  map_add' x y := TrivSqZeroExt.ext (map_add _ _ _) (map_add D _ _)
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact map_mul _ _ _
    · change D (x * y) = algebraMap A B x * D y + D x * algebraMap A B y
      rw [Derivation.leibniz]
      simp only [Algebra.smul_def, mul_comm (algebraMap A B y)]

theorem exists_derivation_extension_of_formallySmooth
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Algebra.FormallySmooth A B] (D : Derivation k A B) :
    ∃ E : Derivation k B B, ∀ x : A, E (algebraMap A B x) = D x := by
  let f := derivationDualHom D
  let : Algebra A (TrivSqZeroExt B B) := f.toAlgebra
  let π : TrivSqZeroExt B B →ₐ[A] B :=
    { (TrivSqZeroExt.fstHom B B B).toRingHom with commutes' := fun _ => rfl }
  have hsurj : Function.Surjective π := fun b => ⟨⟨b, 0⟩, rfl⟩
  have hnil : IsNilpotent (RingHom.ker π.toRingHom) := by
    have hmul : RingHom.ker π.toRingHom * RingHom.ker π.toRingHom ≤
        (⊥ : Ideal (TrivSqZeroExt B B)) := by
      rw [Ideal.mul_le]
      intro x hx y hy
      change (x * y) = 0
      change x.fst = 0 at hx
      change y.fst = 0 at hy
      apply TrivSqZeroExt.ext <;> simp [hx, hy]
    exact ⟨2, (pow_two (RingHom.ker π.toRingHom)).trans (le_antisymm hmul bot_le)⟩
  let h : B →ₐ[A] TrivSqZeroExt B B :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id A B) π hsurj hnil
  have hfst (b : B) : (h b).fst = b :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id A B) π hsurj hnil b
  have hbase (a : A) : h (algebraMap A B a) = f a := h.commutes a
  let E : Derivation k B B :=
    { toFun := fun b => (h b).snd
      map_add' := fun b c => congrArg TrivSqZeroExt.snd (h.map_add b c)
      map_smul' := by
        intro c b
        change (h (c • b)).snd = c • (h b).snd
        rw [Algebra.smul_def c b]
        have hc : (h (algebraMap k B c)).snd = 0 := by
          rw [IsScalarTower.algebraMap_apply k A B c, hbase]
          exact D.map_algebraMap c
        rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hc, smul_zero, add_zero]
        exact (Algebra.smul_def c (h b).snd).symm
      map_one_eq_zero' := by
        change (h 1).snd = 0
        rw [map_one]
        rfl
      leibniz' := by
        intro b c
        change (h (b * c)).snd = b * (h c).snd + c * (h b).snd
        rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
        change b * (h c).snd + (h b).snd * c = _
        rw [mul_comm (h b).snd c] }
  refine ⟨E, fun a => ?_⟩
  change (h (algebraMap A B a)).snd = D a
  rw [hbase]
  rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SmoothDerivationExtension.Construction
