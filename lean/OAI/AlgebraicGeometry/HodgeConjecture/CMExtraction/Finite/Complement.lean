import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Complement -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.Complement.Weil

noncomputable section

/-! The finite complement of a specified real lift in PoissonAutomorphy's actual
central product. The complement is unique and is a group homomorphism. -/

open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA G : Type*} [Group MpR] [Group MpF] [Group MpA] [Group G]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (σ : G →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) (r : G →* MpR)
  (hr : ∀ g, D.real.project (r g) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℝ) (σ g))

include hr in
theorem existsUnique_finiteComplement (g : G) :
    ∃! f : MpF, D.includeReal (r g) * D.includeFinite f = D.rationalSplit (σ g) := by
  obtain ⟨f, hf⟩ := D.decompose (D.rationalSplit (σ g)) (r g)
    ((D.rationalSplit_realProjection (σ g)).trans (hr g).symm)
  refine ⟨f, hf, fun f' hf' => D.includeFinite_injective ?_⟩
  exact mul_left_cancel (hf'.trans hf.symm)

def finiteComplement : G →* MpF where
  toFun g := (existsUnique_finiteComplement D σ r hr g).choose
  map_one' := by
    apply D.includeFinite_injective
    have h := (existsUnique_finiteComplement D σ r hr 1).choose_spec.1
    simpa only [map_one, one_mul] using h
  map_mul' g h := by
    symm
    apply (existsUnique_finiteComplement D σ r hr (g * h)).choose_spec.2
    simp only [map_mul]
    have hg := (existsUnique_finiteComplement D σ r hr g).choose_spec.1
    have hh := (existsUnique_finiteComplement D σ r hr h).choose_spec.1
    exact ((D.commute (r h) ((existsUnique_finiteComplement D σ r hr g).choose))
      |>.mul_mul_mul_comm _ _).trans (congrArg₂ (· * ·) hg hh)

theorem finiteComplement_factorization (g : G) :
    D.includeReal (r g) * D.includeFinite (finiteComplement D σ r hr g) =
      D.rationalSplit (σ g) :=
  (existsUnique_finiteComplement D σ r hr g).choose_spec.1

theorem finiteComplement_covers (g : G) :
    D.finite.project (finiteComplement D σ r hr g) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (σ g) := by
  have h := congrArg
    (fun a => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (D.adelic.project a))
    (finiteComplement_factorization D σ r hr g)
  have hR : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (D.adelic.project (D.includeReal (r g))) = 1 := by
    apply Subtype.ext
    change (D.adelic.project (D.includeReal (r g))).val.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) = 1
    rw [D.includeReal_covers]
    rfl
  have hF : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
      (D.adelic.project (D.includeFinite (finiteComplement D σ r hr g))) =
      D.finite.project (finiteComplement D σ r hr g) := by
    apply Subtype.ext
    change (D.adelic.project (D.includeFinite _)).val.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) = _
    rw [D.includeFinite_covers]
    rfl
  have hQ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (D.adelic.project (D.rationalSplit (σ g))) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (σ g) := by
    rw [D.rationalSplit_covers]
    apply Subtype.ext
    ext i j
    rfl
  simpa only [map_mul, hR, hF, hQ, one_mul] using h

theorem finiteComplement_tensor (g : G) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz ι) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    D.rationalAction (σ g) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor (D.real.action (r g) f) (D.finite.action (finiteComplement D σ r hr g) φ) := by
  change D.adelic.action (D.rationalSplit (σ g)) _ = _
  rw [← finiteComplement_factorization D σ r hr g]
  exact D.factorization _ _ _ _

theorem finiteComplement_eq_finiteLift (g : G)
    (h : r g = D.normalizedRealLift (σ g)) :
    finiteComplement D σ r hr g = D.finiteLift (σ g) := by
  apply D.finiteLift_unique
  rw [← h]
  exact finiteComplement_factorization D σ r hr g

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.Complement.Weil
