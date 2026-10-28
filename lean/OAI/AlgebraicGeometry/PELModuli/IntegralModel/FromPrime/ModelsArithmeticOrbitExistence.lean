import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticComplexCoveredExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReducedOrbit
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.RelabelBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.AffineOrbits

/-! # Models Arithmetic Orbit Existence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsArithmeticOrbitExistence.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_arithmetic_prime_pel_model_with_affine_orbits
    (h43 : ReferenceFamily.ModuliInput)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K] (iota : E →+* K) (κ : K →+* ℂ)
    (hemb : κ.comp iota = P.μ) (N : ℕ) (hN : 3 ≤ N)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    ∃ B : Base.ArithmeticBaseExtension K κ, IsUnit (N : B.R) ∧
      ∃ p : ℕ, ∃ hp : p.Prime, 3 ≤ p ∧ Nat.Coprime p N ∧
        Nat.Coprime p (∏ i, P.polarizationType i) ∧ IsUnit (p : B.R) ∧
        let _ : Fact p.Prime := ⟨hp⟩
        ∃ V : Over B.base, ∃ hred : IsReduced V.left, let _ : IsReduced V.left := hred
          IsNoetherian V.left ∧ LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom ∧
          ∃ U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V,
            ∃ hU : U.IsFine, U.PrescribedRigid ∧
              (∃ e : (Over.pullback B.generic).obj V ≅ Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p,
                Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeUniversal B M p).pullback e.hom)
                  (U.genericIntegralFamily B iota))) ∧
              ∀ x : V.left, ∃ W : V.left.Opens, IsAffineOpen W ∧
                ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source V (3 * s) p).left
                  (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left x y → y ∈ W := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨B, _, p, hp, hp3, hpN, hpδ, hpB, X, hr, _, hft, hqc, hsep, U, hU,
      hrigid, _, hredC, I, hI, V, hV, hInv, hcover⟩ :=
    ArithmeticComplexCoveredExistence.FromPrimeModels.exists_arithmetic_prime_complex_covered_pel_model h43 hPresentations
      s hs hdegree P hP iota κ hemb N hN M hM
  have : Fact p.Prime := ⟨hp⟩
  have : Finite I := hI
  have : IsReduced X.left := hr
  have : LocallyOfFiniteType X.hom := hft
  have : QuasiCompact X.hom := hqc
  have : IsSeparated X.hom := hsep
  let φC := B.embedding.comp B.toField
  let : Algebra B.R ℂ := φC.toAlgebra
  have : IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom φC))).obj X).left := hredC
  have hstable : ∀ σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) p, ∀ i,
      ((Over.pullback (Spec.map (CommRingCat.ofHom φC))).map (U.auxiliaryRelabelMap hU σ)).left ⁻¹ᵁ V i = V i := by
    intro σ i
    rw [U.auxiliaryRelabelMap_baseChange hU φC σ]
    exact ((IntegralAuxiliary.AffineOrbits.IntegralAuxiliaryAction.invariant_iff_relabel (U.baseChange φC)
      (IntegralAdded.FineBaseChange.integralAddedPEL_fine_baseChange U hU φC) (V i)).mp (hInv i)) σ
  obtain ⟨C, hNC, ψ, Z, hrZ, hnZ, hftZ, hqcZ, hsepZ, A, hA, hrigidA, hOrbit⟩ :=
    Arithmetic.ReducedOrbit.arithmetic_reduced_pel_affine_orbit_model iota B U hU hrigid rfl V hV hcover hstable
  have : IsReduced Z.left := hrZ
  have : LocallyOfFiniteType Z.hom := hftZ
  have : QuasiCompact Z.hom := hqcZ
  have hpC : IsUnit (p : C.R) := by simpa only [map_natCast] using hpB.map ψ
  exact ⟨C, hNC, p, hp, hp3, hpN, hpδ, hpC, Z, hrZ, hnZ, hftZ, hqcZ, hsepZ, A, hA,
    hrigidA, Arithmetic.ReferenceComparison.arithmetic_pel_reference_comparison C iota A hA M hM hN hPresentations, hOrbit⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsArithmeticOrbitExistence.FromPrimeModels
