import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieBaseChange

/-! # Reduction Lie -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The prescribed Lie ranks on the actual geometric reduction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j)

theorem Models.RankThreePELModel.GoodIntegralReduction.geometricBase_factors :
    R.geometricBase =
      Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) ≫
        R.specialBase := by
  dsimp only [Models.RankThreePELModel.GoodIntegralReduction.geometricBase, Models.RankThreePELModel.GoodIntegralReduction.specialBase]
  rw [← Spec.map_comp]
  rfl

theorem Models.RankThreePELModel.GoodIntegralReduction.fiberScalar_spec (a : M.Family) (x : R.geom a) :
    Spec.map (CommRingCat.ofHom (R.fiberScalar a x)) =
      R.fiberMap a x ≫ (R.geometricFiber a).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) :=
  Spec.map_preimage _

theorem Models.RankThreePELModel.GoodIntegralReduction.fiberMap_arithmetic_square (a : M.Family) (x : R.geom a) :
    (R.fiberMap a x ≫ R.projection a) ≫ (M.integral a).toOver.hom =
      Spec.map (CommRingCat.ofHom ((R.fiberScalar a x).comp R.residue)) := by
  have hp : R.projection a ≫ (M.integral a).toOver.hom =
      (R.geometricFiber a).hom ≫ R.geometricBase := pullback.condition
  calc
    (R.fiberMap a x ≫ R.projection a) ≫ (M.integral a).toOver.hom =
        R.fiberMap a x ≫ (R.geometricFiber a).hom ≫ R.geometricBase := by
      rw [Category.assoc, hp]
    _ = (R.fiberMap a x ≫ (R.geometricFiber a).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))))) ≫
          R.specialBase := by rw [R.geometricBase_factors]; simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (R.fiberScalar a x)) ≫ R.specialBase := by
      rw [R.fiberScalar_spec]
    _ = Spec.map (CommRingCat.ofHom ((R.fiberScalar a x).comp R.residue)) := by
      dsimp only [Models.RankThreePELModel.GoodIntegralReduction.specialBase]
      rw [← Spec.map_comp]
      rfl

theorem Models.RankThreePELModel.GoodIntegralReduction.lieCharacter_from_arithmetic (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)) :
    R.lieCharacter a x τ =
      ((R.fiberScalar a x).comp R.residue).comp
        ((M.arithmetic.integralEmbedding M.iota).comp
          (NumberField.RingOfIntegers.mapRingHom τ.toRingHom)) := by
  ext z
  have h := congrArg (fun f : NumberField.RingOfIntegers M.arithmetic.extension.carrier →+*
      ZMod q => f (NumberField.RingOfIntegers.mapRingHom
        (M.extendedEmbedding.comp τ.toRingHom) z)) R.residue_compatibility
  apply congrArg (R.fiberScalar a x)
  change j.residue (NumberField.RingOfIntegers.mapRingHom
      (M.extendedEmbedding.comp τ.toRingHom) z) = _
  rw [← h]
  rfl

/-- The geometric rank assertion follows from the integral PEL object's
Lie condition and the canonical comparison of iterated pullbacks. -/
theorem Models.RankThreePELModel.GoodIntegralReduction.hasLieRank_prescribed (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)) :
    R.HasLieRank a x τ ((M.datum a).lieRank τ) := by
  let U := (M.integral a).universal
  have h := U.lieRanks (R.fiberField a x)
    ((R.fiberScalar a x).comp R.residue) (R.fiberMap a x ≫ R.projection a)
    (R.fiberMap_arithmetic_square a x) τ
  have hh := AbelianModuli.ReferenceFamily.LieBaseChange.hasLieRank_pullbackComp U.data.polarized.abelian U.data.action
    (R.projection a) (R.fiberMap a x) _ _ h
  change AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (R.fiberAbelian a x) (R.fiberAction a x)
    (R.lieCharacter a x τ) ((M.datum a).lieRank τ)
  rw [R.lieCharacter_from_arithmetic]
  exact hh

theorem Models.RankThreePELModel.GoodIntegralReduction.active_lieRank_one (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (x : R.geom a) : R.HasLieRank a x (Arithmetic.rationalConjugation E) 1 := by
  have h := R.hasLieRank_prescribed a x (Arithmetic.rationalConjugation E)
  rw [Models.lieRank_conjugation (M.datum a) (hM.2.2 a).1] at h
  exact h

theorem Models.RankThreePELModel.GoodIntegralReduction.compact_lieRank_zero_or_three (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ))
    (h1 : τ ≠ 1) (hc : τ ≠ Arithmetic.rationalConjugation E) :
    R.HasLieRank a x τ 0 ∨ R.HasLieRank a x τ 3 := by
  have h := R.hasLieRank_prescribed a x τ
  rcases Models.lieRank_away_from_changing_pair (M.datum a) (hM.2.2 a).1 τ h1 hc with hr | hr
  · rw [hr] at h
    exact Or.inl h
  · rw [hr] at h
    exact Or.inr h

/-- The complete Lie-rank clause, including a single choice of representatives
for every family and every geometric point. -/
theorem Models.RankThreePELModel.GoodIntegralReduction.exists_representatives_with_lieRanks (hM : M.HasPrescribedBallPeriods) :
    ∃ chosen : Set Gal(E/ℚ), Arithmetic.rationalConjugation E ∈ chosen ∧
      (∀ τ, τ ∈ chosen ↔ Arithmetic.rationalConjugation E * τ ∉ chosen) ∧
      ∀ (a : M.Family) (x : R.geom a),
        R.HasLieRank a x (Arithmetic.rationalConjugation E) 1 ∧
        ∀ τ ∈ chosen, τ ≠ Arithmetic.rationalConjugation E →
          R.HasLieRank a x τ 0 ∨ R.HasLieRank a x τ 3 := by
  obtain ⟨chosen, hc, hp⟩ := Models.exists_conjugate_representatives (E := E)
  refine ⟨chosen, hc, hp, fun a x => ⟨R.active_lieRank_one hM a x, ?_⟩⟩
  intro τ hτ hτc
  apply R.compact_lieRank_zero_or_three hM a x τ _ hτc
  intro h1
  subst τ
  exact (hp 1).mp hτ (by simpa only [mul_one] using hc)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
