import OAI.AlgebraicGeometry.PELModuli.CMPoints.SectionGenericIso
import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryCM
import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryFromFactorization

/-! # Integral Ordinary -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! Ordinary specialization of the actual PEL family along the
constructed integral CM section, at every sufficiently large split prime. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Models.RankThreePELModel.CMSpreadData.IntegralComponentData.exists_ordinary_bound
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    {M : Models.RankThreePELModel E K} {hM : M.HasPrescribedBallPeriods}
    {a : M.Family} {t : Fin (M.componentCount a)} {C : M.CMSpreadData hM a t}
    (T : C.IntegralComponentData)
    :
    ∃ D : ℕ, 0 < D ∧ ∀ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      ∀ j : Arithmetic.QadicChoice T.base.extension.carrier T.base.embedding q,
        j.HasSplitCoordinates C.coefficientEmbedding → D < q →
        q.Coprime (∏ i, (M.datum a).polarizationType i) →
        ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (p : Spec (.of k) ⟶ T.base.base),
          Nat.card ((T.polarized.abelian.pullback p).torsionPoints q
            (Over.mk (𝟙 (Spec (.of k))))) = q ^ (3 * M.s) := by
  let : IsDomain T.base.R := Function.Injective.isDomain T.base.toField T.base.toField_injective
  let : ConnectedSpace T.base.base := inferInstanceAs (ConnectedSpace (Spec (.of T.base.R)))
  have hex (i : Fin 3) := OrdinaryCM.exists_fullCM_heightOne_bound
    (κ := T.base.embedding) C.coefficientEmbedding (T.factor i) (T.action i)
    T.base.complexPoint (T.projective i) (IntegralModel.CMIntegralModel.coefficient_degree (E := E))
  choose D hD hheight using hex
  let B := max ((∑ i, D i) + 1) T.splitting.multiplier
  refine ⟨B, lt_of_lt_of_le (Nat.succ_pos _) (le_max_left _ _), fun q hq => ?_⟩
  let : Fact q.Prime := ⟨hq⟩
  intro j hsplit hb hgood k hk halg hchar p
  have hmult : q.Coprime T.splitting.multiplier := hq.coprime_iff_not_dvd.mpr (by
    intro hdvd
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_right _ _) hb))
      (Nat.le_of_dvd T.splitting.positive hdvd))
  have hdegree : Fintype.card (Fin 3) * Module.finrank ℚ E = 2 * (3 * M.s) := by
    rw [Fintype.card_fin, hM.2.1]
    omega
  apply OrdinaryFromFactorization.ordinary_count_of_scalar_factor_heightOne j C.coefficientEmbedding hsplit
    (T.polarized.pullback p) (fun i => (T.factor i).pullback p)
    (fun i => (T.action i).pullback p) (T.splitting.pullback p) hgood hmult hdegree
  intro i τ
  have hi : D i ≤ ∑ i, D i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact hheight i q hq j hsplit
    (lt_of_le_of_lt ((hi.trans (Nat.le_succ _)).trans (le_max_left _ _)) hb)
    (PolarizedTorsionFiniteness.scalar_factor_torsion_finite_locally_free T.splitting
      (PolarizedTorsionFiniteness.polarized_torsion_finite_locally_free T.polarized hq.pos) hmult i) k p τ

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
