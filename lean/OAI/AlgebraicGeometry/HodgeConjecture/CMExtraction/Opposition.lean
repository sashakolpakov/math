import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LongestWeyl
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeIntegralConjugation

/-! # Opposition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Opposition.Iwasawa

noncomputable section

/-! Integral Weyl conjugation turns inverse transpose into a
Borel-preserving automorphism. Its Iwasawa heights are negative reversal. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime]

def opposition : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q ≃* RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q :=
  (Contragredient.Local.contragredientEquiv ℚ_[q]).trans (MulAut.conj (LongestWeyl.Local.longestWeyl ℚ_[q]))

theorem opposition_apply (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    opposition q g = LongestWeyl.Local.longestWeyl ℚ_[q] * Contragredient.Local.contragredient ℚ_[q] g * (LongestWeyl.Local.longestWeyl ℚ_[q])⁻¹ := rfl

theorem opposition_integral_iff (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    opposition q g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q ↔ g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q := by
  rw [opposition_apply,
    (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).mul_mem_cancel_right
      ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).inv_mem (LongestWeyl.Local.longestWeyl_integral q)),
    (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).mul_mem_cancel_left (LongestWeyl.Local.longestWeyl_integral q),
    Contragredient.Local.contragredient_integral_iff]

theorem opposition_entry (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (i j : Fin 3) :
    (opposition q g).val i j =
      LongestWeyl.Local.reversalSign ℚ_[q] i * LongestWeyl.Local.reversalSign ℚ_[q] j * (g⁻¹).val j.rev i.rev := by
  rw [opposition_apply, LongestWeyl.Local.longestWeyl_inv]
  change (LongestWeyl.Local.longestWeylMatrix ℚ_[q] * (g⁻¹).val.transpose * LongestWeyl.Local.longestWeylMatrix ℚ_[q]) i j = _
  rw [LongestWeyl.Local.longestWeyl_conjugation_entry]
  rfl

theorem opposition_diagonal (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (i : Fin 3) :
    (opposition q g).val i i = (g⁻¹).val i.rev i.rev := by
  rw [opposition_entry]
  by_cases hi : i = 1 <;> simp [LongestWeyl.Local.reversalSign, hi]

theorem opposition_borel (b : Borel.Iwasawa.upperBorel q) : opposition q b.val ∈ Borel.Iwasawa.upperBorel q := by
  intro i j hij
  change (opposition q b.val).val i j = 0
  rw [opposition_entry]
  have hrev : i.rev < j.rev := Fin.rev_lt_rev.mpr hij
  have hz : (b.val⁻¹).val j.rev i.rev = 0 := (b⁻¹).property hrev
  rw [hz, mul_zero]

def oppositionBorel : Borel.Iwasawa.upperBorel q →* Borel.Iwasawa.upperBorel q where
  toFun b := ⟨opposition q b.val, opposition_borel q b⟩
  map_one' := Subtype.ext (opposition q).map_one
  map_mul' b c := Subtype.ext ((opposition q).map_mul b.val c.val)

theorem opposition_valuation (b : Borel.Iwasawa.upperBorel q) (i : Fin 3) :
    (Borel.Iwasawa.borelValuation q (oppositionBorel q b)).toAdd i = -(Borel.Iwasawa.borelValuation q b).toAdd i.rev := by
  change ((opposition q b.val).val i i).valuation = _
  rw [opposition_diagonal]
  have hd : (b.val⁻¹).val i.rev i.rev = ((Borel.Iwasawa.diagonal q b i.rev : ℚ_[q])⁻¹) := by
    change (Borel.Iwasawa.diagonal q b⁻¹ i.rev : ℚ_[q]) = _
    rw [map_inv]
    rfl
  rw [hd, Padic.valuation_inv]
  rfl

theorem opposition_height (x : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (i : Fin 3) :
    (Borel.Iwasawa.decomposition q).height
      (HeckeAutomorphism.Local.cosetAutomorphism (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (opposition q) (opposition_integral_iff q) x) i =
        -(Borel.Iwasawa.decomposition q).height x i.rev := by
  let b := (Borel.Iwasawa.decomposition q).representative x
  have hx : HeckeAutomorphism.Local.cosetAutomorphism (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (opposition q) (opposition_integral_iff q) x =
      QuotientGroup.mk (oppositionBorel q b).val := by
    rw [← (Borel.Iwasawa.decomposition q).representative_spec x, HeckeAutomorphism.Local.cosetAutomorphism_mk]
    rfl
  rw [hx]
  exact (congrFun ((Borel.Iwasawa.decomposition q).height_mk (oppositionBorel q b)) i).trans
    (opposition_valuation q b i)

theorem opposition_hecke (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    HeckeAutomorphism.Local.heckeAutomorphism (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (opposition q) (opposition_integral_iff q) T =
      HeckeAutomorphism.Local.heckeAutomorphism (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Contragredient.Local.contragredientEquiv ℚ_[q])
        (Contragredient.Local.contragredient_integral_iff q) T :=
  HeckeIntegralConjugation.Local.heckeAutomorphism_integral_conjugation (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Contragredient.Local.contragredientEquiv ℚ_[q])
    (opposition q) (Contragredient.Local.contragredient_integral_iff q) (opposition_integral_iff q)
    (LongestWeyl.Local.longestWeyl ℚ_[q]) (LongestWeyl.Local.longestWeyl_integral q) (opposition_apply q) T

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Opposition.Iwasawa
