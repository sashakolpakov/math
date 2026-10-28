import OAI.ArithmeticGeometry.Descent.CMVariety.ContinuousPeriods
import OAI.ArithmeticGeometry.Descent.CMVariety.IntegralMarkedMaps

/-! # Equivariant Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.EquivariantRigidity.Abelian.IntrinsicPeriods

noncomputable section

/-!
The isomorphisms furnished by actual marked CM rigidity preserve all
specified algebraic endomorphisms. This is deduced from the rational
marking comparison and H¹ faithfulness, and is not assumed in the period
classification. Polarization/level comparison and local uniformization
of arithmetic abelian families remain separate geometric obligations.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Topology

variable {Index : Type} [Fintype Index]

/-- Actual algebraic group isomorphism respecting both the full marked
period map and the designated endomorphisms. -/
def HasMarkedEquivariantIso {r : ℕ} (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B)
    (g : Fin r → (A.toOver ⟶ A.toOver)) (k : Fin r → (B.toOver ⟶ B.toOver)) : Prop :=
  ∃ e : A.toOver ≅ B.toOver, IsMonHom e.hom ∧
    (∀ z : Index → ℂ,
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom
        (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap a z))) =
          AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z))) ∧
    ∀ i, g i ≫ e.hom = e.hom ≫ k i

theorem hasMarkedEquivariantIso_of_marked_iso {r : ℕ} {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B)
    (g : Fin r → (A.toOver ⟶ A.toOver)) (k : Fin r → (B.toOver ⟶ B.toOver))
    (hg : ∀ i, IsMonHom (g i)) (hk : ∀ i, IsMonHom (k i))
    (hmatrix : ∀ i, MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism a (g i) = MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism b (k i))
    (hiso : MarkedPeriodClassification.Abelian.IntrinsicPeriods.HasMarkedGroupIso A B a b) : HasMarkedEquivariantIso A B a b g k := by
  obtain ⟨e, he, hp⟩ := hiso
  let : IsMonHom e.hom := he
  refine ⟨e, he, hp, fun i => ?_⟩
  let : IsMonHom (g i) := hg i
  let : IsMonHom (k i) := hk i
  exact IntegralMarkedMaps.Abelian.IntrinsicPeriods.marked_map_equivariant a b e.hom hp (g i) (k i) (hmatrix i)

/-- The finite enhancement constructed from an actual CM abelian variety
is rigid as an endomorphism-enhanced object in its marked transverse chart. -/
theorem hasCMH1_marked_equivariant_rigidity (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (hCM : A.HasCMH1)
    (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) :
    ∃ (HA : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)),
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 A.variety HA ∧
      ∃ (r : ℕ) (g : Fin r → (A.toOver ⟶ A.toOver)),
        (∀ i, IsMonHom (g i)) ∧
        ∀ (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B)
          (HB : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (B.variety.rationalCohomology 1)),
          AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 B.variety HB →
          ∀ k : Fin r → (B.toOver ⟶ B.toOver),
            (∀ i, IsMonHom (k i)) →
            (∀ i, MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism a (g i) = MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism b (k i)) →
            IsCompl (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b HB).holomorphic
              (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a HA).antiholomorphic →
            HasMarkedEquivariantIso A B a b g k := by
  obtain ⟨HA, hHA, r, g, hg, hrigid⟩ := MarkedRigidity.Abelian.IntrinsicPeriods.hasCMH1_marked_local_rigidity A hCM a
  refine ⟨HA, hHA, r, g, hg, ?_⟩
  intro B b HB hHB k hk hmatrix htransverse
  exact hasMarkedEquivariantIso_of_marked_iso a b g k hg hk hmatrix
    (hrigid B b HB hHB k hmatrix htransverse)

/-- In a continuously framed marked family, the constructed enhancement
is locally constant up to actual equivariant algebraic group isomorphism. -/
theorem continuous_marked_family_locally_equivariant
    {S : Type} [TopologicalSpace S]
    (A : S → AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ∀ s, MarkedAbelianPeriods.IntrinsicPeriods.Marking Index (A s))
    (H : ∀ s, AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((A s).variety.rationalCohomology 1))
    (hH : ∀ s, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 (A s).variety (H s))
    (d : ℕ) (frame : S → (Fin d → ℂ) →L[ℂ] (Index → ℂ))
    (hframe : ∀ s, (frame s).toLinearMap.range =
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure (b s) (H s)).holomorphic.map MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates.toLinearMap)
    (s₀ : S) (hcont : ContinuousAt frame s₀) (hinj : Function.Injective (frame s₀))
    (hCM : (A s₀).HasCMH1) :
    ∃ (r : ℕ) (g : Fin r → ((A s₀).toOver ⟶ (A s₀).toOver)),
      (∀ i, IsMonHom (g i)) ∧
      ∀ k : ∀ s, Fin r → ((A s).toOver ⟶ (A s).toOver),
        (∀ s i, IsMonHom (k s i)) →
        (∀ s i, MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s₀) (g i) = MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s) (k s i)) →
        ∀ᶠ s in 𝓝 s₀,
          HasMarkedEquivariantIso (A s₀) (A s) (b s₀) (b s) g (k s) := by
  obtain ⟨r, g, hg, hrigid⟩ :=
    ContinuousPeriods.Abelian.IntrinsicPeriods.continuous_marked_family_locally_isomorphic A b H hH d frame hframe s₀ hcont hinj hCM
  refine ⟨r, g, hg, ?_⟩
  intro k hk hmatrix
  filter_upwards [hrigid k hmatrix] with s hs
  exact hasMarkedEquivariantIso_of_marked_iso (b s₀) (b s) g (k s) hg (hk s) (hmatrix s) hs

end

end OAI.ArithmeticGeometry.Descent.CMVariety.EquivariantRigidity.Abelian.IntrinsicPeriods
