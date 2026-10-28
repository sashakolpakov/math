import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Levels

/-! # Universal -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Universal.FramedPolynomialUniversal

noncomputable section

/-!
# Uniqueness of native maps into framed polynomial envelope levels

Preservation of the lifted coordinates determines the polynomial map.
The proved PD-envelope universal property then determines the ambient
map, and the specified immersion determines the residual map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)
  (P : FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ (fun i => r (MvPolynomial.X i)))
  (n : ℕ)

local notation "W" => WittVector p k
local notation "A" => MvPolynomial σ W
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Levels.FramedPolynomialLevels.level p k B σ r hr hbase n
local notation "l" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Levels.FramedPolynomialLevels.polynomialLift p k B σ r P

theorem reducedMap_eq (g : P ⟶ L) : g.hom.reducedMap = AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P.base := by
  have hg := g.hom.over_X
  change Spec.map (CommRingCat.ofHom g.hom.reducedMap.toRingHom) ≫ 𝟙 _ = P.base.immersion at hg
  rw [Category.comp_id] at hg
  have he := Spec.map_injective (hg.trans (AffineFrameCover.CrystallineAffineFrameCover.residualMap_spec p k B P.base).symm)
  exact AlgHom.ext (ConcreteCategory.congr_hom he)

theorem coefficients_eq (g : P ⟶ L) :
    g.hom.ambientMap.comp (Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficientAlgHom p k B A r hr hbase n) = l := by
  apply MvPolynomial.algHom_ext
  intro i
  change g.hom.ambientMap (Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B A r hr hbase n (MvPolynomial.X i)) =
    MvPolynomial.aeval P.coordinate (MvPolynomial.X i)
  rw [MvPolynomial.aeval_X]
  exact g.coordinate_comm i

theorem unique (hn : (p : P.base.thickening.ring) ^ (n + 1) = 0) (g : P ⟶ L) :
    g = Levels.FramedPolynomialLevels.map p k B σ r hr hbase P n hn := by
  apply FramedCrystalline.Category.FramedCrystallineCategory.hom_ext
  apply Site.Object.Hom.ext
  · exact reducedMap_eq p k B σ r hr hbase P n g
  · exact Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.frameMap_unique p k B A r hr hbase P.base.residueRing P.base.thickening
      (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P.base) l
      (Levels.FramedPolynomialLevels.polynomialLift_reduction p k B σ r hbase P) n hn g.hom.ambientMap g.hom.dp_comp
      (DFunLike.congr_fun (coefficients_eq p k B σ r hr hbase P n g))

theorem p_pow_eq_zero_of_map (g : P ⟶ L) : (p : P.base.thickening.ring) ^ (n + 1) = 0 := by
  have hp : (p : (L).base.thickening.ring) ^ (n + 1) = 0 :=
    Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.p_pow_eq_zero p k B A r hr hbase n
  have h := congrArg g.hom.ambientMap hp
  simpa only [map_pow, map_natCast, map_zero] using h

instance hom_subsingleton : Subsingleton (P ⟶ L) where
  allEq g h :=
    (unique p k B σ r hr hbase P n (p_pow_eq_zero_of_map p k B σ r hr hbase P n g) g).trans
      (unique p k B σ r hr hbase P n (p_pow_eq_zero_of_map p k B σ r hr hbase P n g) h).symm

theorem existsUnique (hn : (p : P.base.thickening.ring) ^ (n + 1) = 0) : ∃! _g : P ⟶ L, True :=
  ⟨Levels.FramedPolynomialLevels.map p k B σ r hr hbase P n hn, trivial,
    fun g _ => unique p k B σ r hr hbase P n hn g⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Universal.FramedPolynomialUniversal
