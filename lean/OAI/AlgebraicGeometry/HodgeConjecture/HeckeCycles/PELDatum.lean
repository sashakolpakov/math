import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralTrace
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum
import OAI.Geometry.ComplexBall.Fields

/-! # PEL Datum -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELDatum.CM

/-! Construct ReferenceFamily's admissible reference PEL datum from the actual source
ball and the explicit CongruenceLevel theorem. Its integral form and polarization type
are constructed, including the actual cokernel identification. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralTrace.CM

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

theorem source_anisotropic (B : GeometricSource.CM.BallDatum E) :
    ∀ x : GeometricSource.CM.Vec E, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian B.b x x = 0 → x = 0 := by
  obtain ⟨τ, hτ1, hτc⟩ := B.other_place
  exact Geometry.ComplexBall.Fields.ArithmeticQuotient.anisotropic_of_definite_embedding B.b
    (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ).toRingHom (B.definite τ hτ1 hτc)

/-- The source's actual Hermitian coefficient supplies an admissible PEL
datum for ReferenceFamily. The reference signs may be chosen independently of theta. -/
theorem admissible_reference_datum
    (B : GeometricSource.CM.BallDatum E) (places : GeometricSource.CM.Places E)
    (h_CongruenceLevel : ReferenceDatum.CM.CongruenceLevelInput E places.count) (dref : Fin places.count → Bool) :
    ∃ P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count,
      P.IsAdmissible ∧ P.b = B.b ∧ P.embeddings = ReferenceDatum.CM.embeddings E places ∧
        P.distinguished = places.distinguished ∧ P.compactSigns = dref := by
  obtain ⟨δ, m, Λ, F, hδ, hδc, hm, hΛ, hint, halt, hnd, _, _, hhol, hperiod, _⟩ :=
    ReferenceDatum.CM.reference_datum_from_source E B places h_CongruenceLevel dref
  let R := IntegralTrace.CM.rationalTraceForm E B.b δ m
  have hintR : ∀ x y : Λ, ∃ n : ℤ, R x.val y.val = (n : ℚ) := by
    intro x y
    rw [IntegralTrace.CM.rationalTraceForm_apply]
    exact hint x.val x.property y.val y.property
  let Z := IntegralTrace.CM.integralRestriction R Λ hintR
  have hRalt : R.IsAlt := by
    intro x
    rw [IntegralTrace.CM.rationalTraceForm_apply]
    exact halt x
  have hRnd : ∀ x, (∀ y, R x y = 0) → x = 0 := by
    intro x hx
    apply hnd x
    intro y
    simpa only [R, IntegralTrace.CM.rationalTraceForm_apply] using hx y
  have hZalt : Z.IsAlt := IntegralTrace.CM.integralRestriction_isAlt R Λ hintR hRalt
  have hZnd : ∀ x : Λ, (∀ y, Z x y = 0) → x = 0 :=
    IntegralTrace.CM.integralRestriction_left_nondegenerate R Λ hintR hΛ.2.1 hRnd
  let : Submodule.IsLattice ℚ Λ := ⟨hΛ.1, hΛ.2.1⟩
  obtain ⟨k, d, hkdim, hdpos, hdchain, hdcoker⟩ :=
    AlternatingPolarization.CM.PolarizationType.polarization_type_exists hZalt hZnd
  have hrank : Module.finrank ℤ Λ = Module.finrank ℚ (GeometricSource.CM.Vec E) :=
    congrArg Cardinal.toNat (Submodule.IsLattice.rank' ℚ Λ)
  have hdegree := (ReferenceDatum.CM.source_degree E places).2
  have hrank' : Module.finrank ℤ Λ = 6 * places.count := by
    rw [hrank]
    simp only [GeometricSource.CM.Vec, Module.finrank_pi_fintype, hdegree, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hcount : 2 * k = 6 * places.count := hkdim.symm.trans hrank'
  have hk : k = 3 * places.count := by omega
  subst k
  let P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count := {
    embeddings := ReferenceDatum.CM.embeddings E places
    distinguished := places.distinguished
    compactSigns := dref
    b := B.b
    imaginaryScalar := δ
    denominator := m
    lattice := Λ
    integralForm := Z
    polarizationType := d
    periodFamily := F }
  refine ⟨P, ?_, rfl, rfl, rfl, rfl⟩
  obtain ⟨hb, hb0, hμ, hc⟩ := ReferenceDatum.CM.source_signature E B places
  refine ⟨ReferenceDatum.CM.embeddings_complete E places, hb, hb0, hμ, hc, source_anisotropic E B,
    hδ, hδc, hm, hΛ, ?_, hZalt, hZnd, hdpos, hdchain, hdcoker, ?_, ?_⟩
  · intro x y
    exact (IntegralTrace.CM.integralRestriction_cast R Λ hintR x y).trans
      (IntegralTrace.CM.rationalTraceForm_apply E B.b δ m x.val y.val)
  · simpa only [P, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.domain, Fintype.card_fin] using hhol
  · exact hperiod

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELDatum.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELDatum.CM.ZeroReference

/-! Number the auxiliary reference datum's active block by zero, as in
the ordinary reduction construction. The original source period uses its
own enumeration; only the independently chosen reference datum is relabeled. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

def places (p : GeometricSource.CM.Places E) : GeometricSource.CM.Places E where
  count := p.count
  representative := fun i => p.representative (Equiv.swap ⟨0, (ReferenceDatum.CM.source_degree E p).1⟩ p.distinguished i)
  distinguished := ⟨0, (ReferenceDatum.CM.source_degree E p).1⟩
  identity := by simpa only [Equiv.swap_apply_left] using p.identity
  complete := by
    let e : Fin p.count ≃ Fin p.count := Equiv.swap ⟨0, (ReferenceDatum.CM.source_degree E p).1⟩ p.distinguished
    have h := p.complete.comp (Equiv.prodCongr e (Equiv.refl Bool)).bijective
    convert h using 1
    funext w
    rfl

theorem admissible (B : GeometricSource.CM.BallDatum E) (p : GeometricSource.CM.Places E) (hCongruenceLevel : ReferenceDatum.CM.CongruenceLevelInput E p.count) :
    ∃ P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E p.count,
      P.IsAdmissible ∧ P.b = B.b ∧ P.μ = E.val.toRingHom ∧ P.distinguished.val = 0 := by
  obtain ⟨P, hP, hb, hemb, hdist, _hsign⟩ := admissible_reference_datum
    E B (ZeroReference.places E p) hCongruenceLevel (fun _ => false)
  refine ⟨P, hP, hb, ?_, ?_⟩
  · unfold AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.μ
    rw [hemb, hdist, ReferenceDatum.CM.embeddings_distinguished]
  · exact congrArg Fin.val hdist

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELDatum.CM.ZeroReference

end

end OAI
