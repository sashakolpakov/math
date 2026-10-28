import OAI.Analysis.HodgeTheory.Decomposition.KoszulConnection

/-! # Kahler Koszul -/

namespace OAI.Analysis.HodgeTheory.Decomposition.KahlerKoszul.Constructions

noncomputable section

/-! Closedness and Hermitian symmetry force the constructed torsion-free
metric connection to preserve the complex structure. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E]

theorem koszulFirstKind_J (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (hS : ∀ a b c, T a b c = T a c b)
    (hJ : ∀ a b c, T a (Complex.I • b) c = -T a b (Complex.I • c))
    (hclosed : ∀ a b c,
      T a b (Complex.I • c) - T b a (Complex.I • c) + T c a (Complex.I • b) = 0)
    (u v w : E) : KoszulConnection.Constructions.koszulFirstKind T u (Complex.I • v) w = -KoszulConnection.Constructions.koszulFirstKind T u v (Complex.I • w) := by
  have hJJ (a b c : E) : T a (Complex.I • b) (Complex.I • c) = T a b c := by
    rw [hJ, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, neg_neg]
  have h1 := hclosed v w u
  rw [hS v w (Complex.I • u), hJ v u w, hS w v (Complex.I • u), hJ w u v] at h1
  have h2 := hclosed (Complex.I • v) (Complex.I • w) u
  rw [hJJ, hJJ, hJJ, hS (Complex.I • v) w u, hS (Complex.I • w) v u] at h2
  rw [KoszulConnection.Constructions.koszulFirstKind_apply, KoszulConnection.Constructions.koszulFirstKind_apply, hJ u v w]
  linarith

theorem koszulConnection_J_right (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u)
    (hBJ : ∀ u v, B (Complex.I • u) v = -B u (Complex.I • v))
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (hS : ∀ a b c, T a b c = T a c b)
    (hJ : ∀ a b c, T a (Complex.I • b) c = -T a b (Complex.I • c))
    (hclosed : ∀ a b c,
      T a b (Complex.I • c) - T b a (Complex.I • c) + T c a (Complex.I • b) = 0)
    (u v : E) : KoszulConnection.Constructions.koszulConnection B T u (Complex.I • v) = Complex.I • KoszulConnection.Constructions.koszulConnection B T u v := by
  apply KoszulConnection.Constructions.positive_bilinear_left_ext B hpos
  intro w
  rw [hBJ, KoszulConnection.Constructions.koszulConnection_pair B hpos, KoszulConnection.Constructions.koszulConnection_pair B hpos]
  exact koszulFirstKind_J T hS hJ hclosed u v w

theorem koszulConnection_J_left (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u)
    (hBJ : ∀ u v, B (Complex.I • u) v = -B u (Complex.I • v))
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (hS : ∀ a b c, T a b c = T a c b)
    (hJ : ∀ a b c, T a (Complex.I • b) c = -T a b (Complex.I • c))
    (hclosed : ∀ a b c,
      T a b (Complex.I • c) - T b a (Complex.I • c) + T c a (Complex.I • b) = 0)
    (u v : E) : KoszulConnection.Constructions.koszulConnection B T (Complex.I • u) v = Complex.I • KoszulConnection.Constructions.koszulConnection B T u v := by
  rw [KoszulConnection.Constructions.koszulConnection_symmetric B T hS, koszulConnection_J_right B hpos hBJ T hS hJ hclosed,
    KoszulConnection.Constructions.koszulConnection_symmetric B T hS v u]

end

end OAI.Analysis.HodgeTheory.Decomposition.KahlerKoszul.Constructions
