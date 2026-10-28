import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricPrimeLevel
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.FrameFactorization

/-! # Prime Level Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PrimeLevelCover.IntegralLevelCover

noncomputable section

/-! The actual finite etale prime-level parameter scheme is surjective
over every base where the prime is invertible. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {g p : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) [Fact p.Prime]
    (hp : ∀ x : S, IsUnit (p : S.presheaf.stalk x))

theorem prime_fullFrame_surjective : Surjective (FrameLocus.IntegralLevelCover.fullFrameScheme A hp (N := p)).hom := by
  constructor
  intro x
  let k := AlgebraicClosure (S.residueField x)
  let q : Spec (.of k) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) k)) ≫ S.fromSpecResidueField x
  have hq : q (default : Spec (.of k)) = x := S.fromSpecResidueField_apply x _
  have hpk : ∀ z : Spec (.of k), IsUnit (p : (Spec (.of k)).presheaf.stalk z) := fun z => by
    simpa only [map_natCast] using (hp (q z)).map (q.stalkMap z).hom
  obtain ⟨β⟩ := GeometricPrimeLevel.geometric_exists_prime_fullLevel (A.pullback q) p hpk
  let f := FrameFactorization.IntegralLevelCover.fullFrameOfRelativeLevel A hp (Over.mk q) β
  refine ⟨f.left (default : Spec (.of k)), ?_⟩
  exact (congrArg (fun a : Spec (.of k) ⟶ S => a default) f.w).trans hq

include hp in
theorem exists_prime_fullLevel_cover :
    ∃ (S' : Scheme.{0}) (u : S' ⟶ S), IsFinite u ∧ Etale u ∧ Surjective u ∧
      Nonempty ((A.pullback u).FullLevel p) :=
  ⟨(FrameLocus.IntegralLevelCover.fullFrameScheme A hp).left, (FrameLocus.IntegralLevelCover.fullFrameScheme A hp).hom,
    (FrameLocus.IntegralLevelCover.fullFrameScheme_finite_etale A hp).1, (FrameLocus.IntegralLevelCover.fullFrameScheme_finite_etale A hp).2,
    prime_fullFrame_surjective A hp, ⟨CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel A hp⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PrimeLevelCover.IntegralLevelCover
