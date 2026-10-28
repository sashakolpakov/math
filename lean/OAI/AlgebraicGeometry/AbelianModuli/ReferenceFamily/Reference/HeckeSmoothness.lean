import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ScaledPELQuotients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HeckeSmoothLocus
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PELStratumLocalRegularity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PrimeBallLatticeIsogenies

/-! # Hecke Smoothness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HeckeSmoothness.FinePELModel

noncomputable section

/-! The reference locus is smooth on the actual fine PEL scheme.
A native local period chart supplies one open ball patch of smooth
reference points. Good-prime rational isometries move every reference
point into that patch, and their actual paired PEL quotients preserve
smoothness through the finite étale Hecke correspondence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

attribute [local implicit_reducible] Models.FinePELModel.complexFiber

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [IsGalois ℚ E] [Field K] [NumberField K]
    {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    [LocallyOfFiniteType M.space.hom]

local instance : LocallyOfFinitePresentation (M.complexFiber κ).hom :=
  inferInstanceAs (LocallyOfFinitePresentation
    (Limits.pullback.snd M.space.hom (Spec.map (CommRingCat.ofHom κ))))

omit [IsGalois ℚ E] in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.reference_pairedQuotient_mem_smoothLocus_iff
    (hN : 3 ≤ N) {n : ℕ} (hn : 0 < n) (hcop : Nat.Coprime n N)
    (hmod : Nat.ModEq N n 1)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (z w : P.domain)
    (f : Paired.PELQuotients.PairedPELQuotient (P.referencePELObject hP z iota κ hκ N)
      (P.referencePELObject hP w iota κ hκ N) n) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.referencePoint hM κ hP hκ z) ∈
        (M.complexFiber κ).hom.smoothLocus ↔
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.referencePoint hM κ hP hκ w) ∈
        (M.complexFiber κ).hom.smoothLocus := by
  have : IsLocallyNoetherian M.space.left :=
    LocallyOfFiniteType.isLocallyNoetherian M.space.hom
  have hz : AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap M hM (P.referencePELObject hP z iota κ hκ N) =
      M.complexPointBaseEquiv κ (M.referencePoint hM κ hP hκ z) :=
    (AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap_unique M hM _ _ (M.referencePoint_recovery hM κ hP hκ z)).symm
  have hw : AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap M hM (P.referencePELObject hP w iota κ hκ N) =
      M.complexPointBaseEquiv κ (M.referencePoint hM κ hP hκ w) :=
    (AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap_unique M hM _ _ (M.referencePoint_recovery hM κ hP hκ w)).symm
  simpa only [hz, hw, Equiv.symm_apply_apply] using
    HeckeSmoothLocus.geometric_pair_complexPoints_mem_smoothLocus_iff M hM κ hN hn hcop hmod hdegree f

omit [NumberField K] in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.exists_reference_smooth_ball_patch [QuasiCompact M.space.hom]
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ O : Set Geometry.ComplexBall.PrescribedSignsB.BallChart, IsOpen O ∧ O.Nonempty ∧ O ⊆ P.domain ∧
      ∀ z : P.domain, z.val ∈ O →
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.referencePoint hM κ hP hκ z) ∈
          (M.complexFiber κ).hom.smoothLocus := by
  obtain ⟨R, hR, a, x, hx⟩ :=
    M.exists_reference_smooth_surface_stratum hM κ hP hκ hs hdegree
  let f := Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R
  have hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension R.toOver.hom = 2 :=
    (Intrinsic.SmoothStrata.smoothPiece_dimension (M.complexFiber κ) R).trans hR
  obtain ⟨e, he, _, _, htarget, hmod⟩ :=
    M.exists_native_reference_moduli_chart hM κ hP hκ f hs hdegree hdim x a hx
  refine ⟨e.target, e.open_target, ⟨e x, e.map_source he⟩, htarget, ?_⟩
  intro z hz
  let y := e.symm z.val
  have hy : y ∈ e.source := e.map_target hz
  obtain ⟨hp, hpoint⟩ := hmod y hy
  have hz' : (⟨e y, hp⟩ : P.domain) = z := Subtype.ext (e.right_inv hz)
  rw [hz'] at hpoint
  have hsm := M.complexPoint_mem_smoothLocus_of_surface hP hM κ hκ f y hdim
  rw [hpoint] at hsm
  simpa only [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying,
    Subsingleton.elim ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint (IsLocalRing.closedPoint ℂ)] using hsm

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.referencePoint_mem_smoothLocus [QuasiCompact M.space.hom]
    (hN : 3 ≤ N) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (z : P.domain) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.referencePoint hM κ hP hκ z) ∈
      (M.complexFiber κ).hom.smoothLocus := by
  classical
  obtain ⟨O, hO, ⟨v, hv⟩, hdom, hsmooth⟩ :=
    M.exists_reference_smooth_ball_patch hM κ hP hκ hs hdegree
  let w₀ : P.domain := ⟨v, hdom hv⟩
  have hdata := hP
  rcases hdata with ⟨_, hb, hbne, _, _, _, _, _, _, hlat, _, _, _, hδ, _⟩
  let H : Matrix (Fin 3) (Fin 3) E := Matrix.diagonal ![1, 1, P.b]
  have hHerm : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i) := by
    intro i j
    by_cases hij : i = j
    · subst j
      fin_cases i <;> simp [H, hb]
    · simp [H, Matrix.diagonal, hij, Ne.symm hij]
  have hdet : H.det ≠ 0 := by
    simpa [H, Matrix.det_diagonal, Fin.prod_univ_succ] using hbne
  let e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ) := LinearEquiv.refl ℂ _
  have he : ∀ x y, Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y := by
    intro x y
    rfl
  have hC : 0 < (∏ i, P.polarizationType i) ^ 2 :=
    pow_pos (Finset.prod_pos (fun i _ => hδ i)) 2
  obtain ⟨g, D, m, m', hg, _, hhit, hD, hcopN, hcopδ, hmod, hm, hm', _, _, hcongr, _⟩ :=
    PrimeBallLatticeIsogenies.exists_original_ball_paired_lattice_maps P hP H hHerm hdet P.lattice hlat e he
      N ((∏ i, P.polarizationType i) ^ 2) (NeZero.pos N) hC z w₀ O hO hv
  have hg' : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b) := by
    intro x y
    simpa only [H, Principal.BallAction.matrixHermitian_diagonal] using hg x y
  change P.lineAction g z.val ∈ O at hhit
  let w : P.domain := ⟨P.lineAction g z.val, hdom hhit⟩
  obtain ⟨f⟩ := P.reference_paired_quotient_of_scaled_isometry hP z w iota κ hκ N
    g hg' rfl D hD hmod m m' hm hm' hcongr
  exact (M.reference_pairedQuotient_mem_smoothLocus_iff hM κ hP hκ hN
    (pow_pos hD 2) hcopN hmod hcopδ z w f).mpr (hsmooth w hhit)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HeckeSmoothness.FinePELModel
