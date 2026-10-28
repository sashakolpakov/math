import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.VariableGraphLevelRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GlobalGraphPowerParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementTransportIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ArbitraryBaseProjectivity

/-! # Polarized Noetherian Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An arbitrary affine rational polarized family is pulled back from
an actual Noetherian polarized family. A variable-degree graph embedding
first gives an original full-level Hilbert point; the represented graph
power locus then recovers the original polarization and ordered level.
No Noetherian or reducedness assumption is imposed on the test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem Rational.PolarizedNoetherianModel.rationalBase_nat_isUnit {S : Scheme.{0}} (q : S ⟶ Spec (.of ℚ))
    (n : ℕ) (hn : 0 < n) : IsUnit (n : Γ(S, ⊤)) := by
  have hq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hq).map (Coefficient.ModulePresheaf.schemeCoefficientMap q)

variable {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (q : S ⟶ Spec (.of ℚ)) (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)

include hg hδ hN in
theorem PolarizationData.PolarizedAbelianWithFullLevel.exists_rationalNoetherianModel_of_graphEmbedding
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom) :
    ∃ M : Over (Spec (.of ℚ)), IsNoetherian M.left ∧
      ∃ B : PolarizationData.PolarizedAbelianWithFullLevel g δ N M.left,
        ∃ t : Over.mk q ⟶ M, Nonempty (Moduli.Isomorphisms.LevelPreservingIso A (B.pullback t.left)) := by
  let : NeZero N := ⟨by omega⟩
  have hunit := Rational.PolarizedNoetherianModel.rationalBase_nat_isUnit q N (by omega)
  let M := VariableGraphLevelRecovery.VariableGraphLevel.parameter (Spec (.of ℚ)) A E
  let F := VariableGraphLevelRecovery.VariableGraphLevel.universalFamily (Spec (.of ℚ)) A E
  let P := VariableGraphLevelRecovery.VariableGraphLevel.projective (Spec (.of ℚ)) A E
  let x := VariableGraphLevelRecovery.VariableGraphLevel.point (Spec (.of ℚ)) A hg hN hunit E q
  let e := VariableGraphLevelRecovery.VariableGraphLevel.recovery (Spec (.of ℚ)) A hg hN hunit E q
  let F₀ : Level.Data.AbelianSchemeWithFullLevel g N S := ⟨A.abelian, A.level⟩
  let H₀ : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F₀ (A.graphBundle.tensorPower E.degree) E.degree :=
    ⟨A.dual, A.polarization, ⟨Iso.refl _⟩⟩
  have he : Line.Bundles.LineBundle.pullbackClass e.hom.left
      (Line.Bundles.LineBundle.classOf (P.ampleLineBundle.pullback
        (pullback.fst F.abelian.scheme.hom x.left))) =
      Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower E.degree) :=
    Quotient.sound ⟨VariableGraphLevelRecovery.VariableGraphLevel.recoveryGraphPowerIso (Spec (.of ℚ)) A hg hN hunit E q⟩
  have hl : F₀.level.transport e = (F.pullback x.left).level :=
    VariableGraphLevelRecovery.VariableGraphLevel.recovery_level (Spec (.of ℚ)) A hg hN hunit E q
  let H₁ : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback x.left)
      (P.ampleLineBundle.pullback (pullback.fst F.abelian.scheme.hom x.left)) E.degree :=
    H₀.transportFamily e he
  let H := H₁.normalizeParameter x.left
  have hA : A.classOf = H.object.classOf :=
    (A.classOf_eq_iff H.object).mpr ⟨H₀.transportFamilyModuliIso e he hl⟩
  obtain ⟨z, hz⟩ := (Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.lifts_iff M F P M.hom E.degree E.degree_pos
    δ hδ (Over.mk q) x).mpr ⟨H⟩
  let W := Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.parameter M F P M.hom E.degree E.degree_pos δ hδ
  let B := Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.universalFamily M F P M.hom E.degree E.degree_pos δ hδ
  have hclass := Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.universalFamily_classifies M F P M.hom
    E.degree E.degree_pos δ hδ z
  rw [hz] at hclass
  have hzclass : (B.pullback z.left).classOf = H.object.classOf := hclass H
  exact ⟨W, inferInstance, B, z, (A.classOf_eq_iff (B.pullback z.left)).mp (hA.trans hzclass.symm)⟩

include hg hδ hN in
theorem PolarizationData.PolarizedAbelianWithFullLevel.exists_rationalNoetherianModel [IsAffine S] :
    ∃ M : Over (Spec (.of ℚ)), IsNoetherian M.left ∧
      ∃ B : PolarizationData.PolarizedAbelianWithFullLevel g δ N M.left,
        ∃ t : Over.mk q ⟶ M, Nonempty (Moduli.Isomorphisms.LevelPreservingIso A (B.pullback t.left)) := by
  obtain ⟨E⟩ := A.graphBundle_isAmple_of_affine.exists_powerProjectiveEmbedding A.abelian.scheme.hom
  exact A.exists_rationalNoetherianModel_of_graphEmbedding q hg hδ hN E

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
