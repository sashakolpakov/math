import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelPointFamilyIso

/-! # Level Family Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelFamilyComparison.StableHilbertLevel

noncomputable section

/-! The actual marked-chart family agrees with the original full-level
universal family along the specified forgetful map, including its group,
ordered level, and original projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

variable {T : Over (Spec (CommRingCat.of R))} (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)

instance pointFamilyIso_isMonHom :
    (LevelPointFamilyIso.StableHilbertLevel.pointFamilyRecovery R i j D H hH g Hm Hi N labels u).GroupCompatible :=
  (LevelPointFamilyIso.StableHilbertLevel.pointFamilyRecovery R i j D H hH g Hm Hi N labels u).groupCompatible

theorem pointFamilyIso_level :
    (LevelPointFamilyIso.StableHilbertLevel.pointFamilyRecovery R i j D H hH g Hm Hi N labels u).LevelCompatible :=
  (LevelPointFamilyIso.StableHilbertLevel.pointFamilyRecovery R i j D H hH g Hm Hi N labels u).levelCompatible

theorem pointFamilyIso_embedding_left :
    (LevelPointFamilyIso.StableHilbertLevel.pointFamilyRecovery R i j D H hH g Hm Hi N labels u).NativeEmbeddingCompatible :=
  (LevelPointFamilyIso.StableHilbertLevel.pointFamilyRecovery R i j D H hH g Hm Hi N labels u).nativeEmbeddingCompatible

theorem pointFamilyIso_embedding :
    (LevelPointFamilyIso.StableHilbertLevel.pointFamilyRecovery R i j D H hH g Hm Hi N labels u).EmbeddingCompatible :=
  (LevelPointFamilyIso.StableHilbertLevel.pointFamilyRecovery R i j D H hH g Hm Hi N labels u).embeddingCompatible

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelFamilyComparison.StableHilbertLevel
