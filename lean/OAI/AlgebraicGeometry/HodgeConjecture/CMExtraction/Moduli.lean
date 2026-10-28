import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PreprimeComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.Family
import OAI.RepresentationTheory.Hecke.OrdinaryCharacterIntegralModelOf

/-! # Moduli -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Moduli.Intrinsic

noncomputable section

/-! Choose the full prescribed PEL level and its actual integral model
after the retained test and before the prime. The full ReferenceFamily and IntegralModel
propositions are explicit inputs; no statement theorem is used as evidence. -/

open scoped Classical _root_.Matrix
open _root_.CategoryTheory

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PreprimeComparison.Multiplicity OAI.RepresentationTheory.Hecke.OrdinaryCharacterIntegralModelOf.OrdinaryIntrinsic

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)

structure RetainedModuli where
  level : ℕ
  level_ge_three : 3 ≤ level
  depth_dvd : R.depth ∣ level
  deep : PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P level
  model : AbelianModuli.ReferenceFamily.Models.FinePELModel P (RingHom.id E) level
  fine : model.IsFine
  ballComponents : model.HasProjectiveBallComponents E.val.toRingHom
  principal : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
  principal_mem : ∀ g, g ∈ principal ↔
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice level g ∧ LinearMap.det g.toLinearMap = 1
  torsion_free : ∀ g ∈ principal, ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1
  component : model.ComplexComponent E.val.toRingHom
  variety : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety
  projectiveComponent : model.IsProjectiveComponent E.val.toRingHom component variety
  uniformization : P.IsUniformizedBy variety principal
  integral : RepresentationTheory.Hecke.OrdinaryCharacterIntegralModelOf.OrdinaryIntrinsic.IntegralModel P (RingHom.id E) E.val.toRingHom model

theorem exists_retained_moduli
    (hReferenceFamily : AbelianScheme.IsogenyQuotient.Reference.Family.Construction.ReferenceFamilyInput) (hIntegralModel : RepresentationTheory.Hecke.IntegralModel.OrdinaryCharacterIntrinsic.FullIntegralModelInput)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    Nonempty (RetainedModuli E P hP hμ v hv W R) := by
  have hemb : E.val.toRingHom.comp (RingHom.id E) = P.μ := by
    rw [RingHom.comp_id, hμ]
  obtain ⟨N, hN, hdiv, hlevels⟩ := hReferenceFamily s hs hdegree P hP (RingHom.id E) E.val.toRingHom
    hemb ⊤ R.depth R.depth_pos
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 3) hN
  obtain ⟨hdet, _, Γ, hΓ, htor, M, hM, hball, C₀, X, hX, hunif⟩ :=
    hlevels N hNpos (dvd_refl N)
  have hdeep : PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N := by
    refine ⟨hN, ?_⟩
    intro g hg k hk hpow
    exact htor g ((hΓ g).mpr ⟨hg, hdet g hg⟩) k hk hpow
  exact ⟨{
    level := N
    level_ge_three := hN
    depth_dvd := hdiv
    deep := hdeep
    model := M
    fine := hM
    ballComponents := hball
    principal := Γ
    principal_mem := hΓ
    torsion_free := htor
    component := C₀
    variety := X
    projectiveComponent := hX
    uniformization := hunif
    integral := RepresentationTheory.Hecke.OrdinaryCharacterIntegralModelOf.OrdinaryIntrinsic.integralModelOfFullIntegralModel hIntegralModel hs hdegree hP hemb hdeep hM }⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Moduli.Intrinsic
