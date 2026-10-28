import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.VariableGraphLevelRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementTransportIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ArbitraryBaseProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.UnitDegreeEmbedding

/-! # Degree Polarized Noetherian Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Arbitrary affine polarized families descend to actual Noetherian
families using graph embeddings whose degree is a unit on the original base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] [IsNoetherianRing R]
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}

theorem PolarizationData.PolarizedAbelianWithFullLevel.exists_noetherianModel_of_unitDegreeGraphEmbedding
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (q : S ⟶ Spec (.of R)) (hg : 0 < g) (hδ : ∀ i, 0 < δ i)
    (hN : 3 ≤ N) (hNR : IsUnit (N : R))
    (Φ : ∀ d : ℕ, 0 < d → IsUnit (d : R) → GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
    (hE : IsUnit (E.degree : R)) :
    ∃ M : Over (Spec (.of R)), IsNoetherian M.left ∧
      ∃ B : PolarizationData.PolarizedAbelianWithFullLevel g δ N M.left,
        ∃ t : Over.mk q ⟶ M, Nonempty (Moduli.Isomorphisms.LevelPreservingIso A (B.pullback t.left)) := by
  let : NeZero N := ⟨by omega⟩
  have hunit : IsUnit (N : Γ(S, ⊤)) := by
    simpa only [map_natCast] using hNR.map (Coefficient.ModulePresheaf.schemeCoefficientMap q)
  let M := VariableGraphLevelRecovery.VariableGraphLevel.parameter (Spec (.of R)) A E
  let F := VariableGraphLevelRecovery.VariableGraphLevel.universalFamily (Spec (.of R)) A E
  let P := VariableGraphLevelRecovery.VariableGraphLevel.projective (Spec (.of R)) A E
  let x := VariableGraphLevelRecovery.VariableGraphLevel.point (Spec (.of R)) A hg hN hunit E q
  let e := VariableGraphLevelRecovery.VariableGraphLevel.recovery (Spec (.of R)) A hg hN hunit E q
  let F₀ : Level.Data.AbelianSchemeWithFullLevel g N S := ⟨A.abelian, A.level⟩
  let H₀ : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F₀ (A.graphBundle.tensorPower E.degree) E.degree :=
    ⟨A.dual, A.polarization, ⟨Iso.refl _⟩⟩
  have he : Line.Bundles.LineBundle.pullbackClass e.hom.left
      (Line.Bundles.LineBundle.classOf (P.ampleLineBundle.pullback
        (pullback.fst F.abelian.scheme.hom x.left))) =
      Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower E.degree) :=
    Quotient.sound ⟨VariableGraphLevelRecovery.VariableGraphLevel.recoveryGraphPowerIso (Spec (.of R)) A hg hN hunit E q⟩
  have hl : F₀.level.transport e = (F.pullback x.left).level :=
    VariableGraphLevelRecovery.VariableGraphLevel.recovery_level (Spec (.of R)) A hg hN hunit E q
  let H₁ : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback x.left)
      (P.ampleLineBundle.pullback (pullback.fst F.abelian.scheme.hom x.left)) E.degree :=
    H₀.transportFamily e he
  let H := H₁.normalizeParameter x.left
  have hA : A.classOf = H.object.classOf :=
    (A.classOf_eq_iff H.object).mpr ⟨H₀.transportFamilyModuliIso e he hl⟩
  let D := Φ E.degree E.degree_pos hE M F P
  obtain ⟨z, hz⟩ := (D.lifts_iff (Over.mk q) x).mpr ⟨H⟩
  let B := D.universalFamily
  have hclass := D.universalFamily_classifies E.degree_pos hδ z
  rw [hz] at hclass
  have hzclass : (B.pullback z.left).classOf = H.object.classOf := hclass H
  exact ⟨D.parameter, (D.quasiProjective (VariableGraphLevelRecovery.VariableGraphLevel.quasiProjective
    (Spec (.of R)) A E)).noetherian, B, z,
      (A.classOf_eq_iff (B.pullback z.left)).mp (hA.trans hzclass.symm)⟩

theorem PolarizationData.PolarizedAbelianWithFullLevel.exists_noetherianModel_over_spec
    (C : CommRingCat) (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec C))
    (q : Spec C ⟶ Spec (.of R)) (hg : 0 < g) (hδ : ∀ i, 0 < δ i)
    (hN : 3 ≤ N) (hNR : IsUnit (N : R))
    (Φ : ∀ d : ℕ, 0 < d → IsUnit (d : R) → GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ) :
    ∃ M : Over (Spec (.of R)), IsNoetherian M.left ∧
      ∃ B : PolarizationData.PolarizedAbelianWithFullLevel g δ N M.left,
        ∃ t : Over.mk q ⟶ M, Nonempty (Moduli.Isomorphisms.LevelPreservingIso A (B.pullback t.left)) := by
  obtain ⟨k, E, hE⟩ := A.graphBundle_isAmple_of_affine.exists_powerDegreeEmbedding
    (f := A.abelian.scheme.hom) N (by omega)
  have hunit : IsUnit (E.degree : R) := by
    rw [hE, Nat.cast_pow]
    exact hNR.pow k
  exact A.exists_noetherianModel_of_unitDegreeGraphEmbedding q hg hδ hN hNR Φ E hunit

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
