import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELUniversalFunctions
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Correspondence

/-! # Integral Hecke -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntegralHecke.Construction

noncomputable section

/-! Full integral Hecke realizations on ReferenceFamily's original fine model:
one finite etale parameter represents all subgroup choices, its actual
fine target has the full polarized PEL isogeny, its kernel is maximal
isotropic on every test, and its fibers equal the independent raw
double-coset multisets with multiplicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] [CharZero K] [Field L] [NumberField L]
    {d N q : ℕ} [NeZero N] [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
    (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine) (κ₀ : K →+* ℂ)
    (hC : Z.HasProjectiveBallComponents κ₀)
    {κ : L →+* ℂ} (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
    (hsplit : j.HasSplitCoordinates arithmeticEmbedding)
    (hd : 0 < d) (hdegree : Module.finrank ℚ E = 2 * d)
    (h : ℕ) (labels : ChoiceKernel.Construction.KernelIndex d ≃ Gal(E/ℚ))
    (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
    (a : Fin d → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v))
    (hcop : Nat.Coprime q N) (hpol : Nat.Coprime q (∏ i, P.polarizationType i))
    (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0})

def IntegralHeckeFamily : Prop :=
  let A := Z.universal
  let hA := FinePELUniversalFunctions.Construction.finePEL_universal_hasUniversalGlobalFunctions Z hZ κ₀ hC
  let M := fun v => ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)
  letI : ∀ v, Module (ZMod (q ^ h)) (M v) :=
    fun v => ElementaryModules.Construction.rankThreeElementaryModule_structure q h (a v) (ha v)
  let p := CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
  let r := CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
  let b := UniversalFunction.PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A.polarized.abelian A.polarized.dual
    A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA)
      (q ^ h) (pow_pos (Fact.out : q.Prime).pos h)
  let ep := CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels b
  ∃ Q : Over Z.space.left, IsFinite Q.hom ∧ Etale Q.hom ∧
    ∃ repr : (Parameter.Products.Construction.blockTupleFunctor d (fun v =>
      SubgroupFunctor.Construction.supportedSubgroupFunctor A.polarized.abelian.scheme (q ^ h) (M v) (p v))).RepresentableBy Q,
    ∃ e : uliftYoneda.{1}.obj (TotalParameters.Construction.totalParameter Z.space Q) ≅
      TotalParameters.Construction.totalParameterFunctor Z.space Q _ repr,
    e.hom ≫ TotalParameters.Construction.totalParameterForget Z.space Q _ repr =
      uliftYoneda.{1}.map (TotalParameters.Construction.totalParameterSource Z.space Q) ∧
    IsFinite (TotalParameters.Construction.totalParameterSource Z.space Q).left ∧
    Etale (TotalParameters.Construction.totalParameterSource Z.space Q).left ∧
    let F := ChoiceKernel.Construction.choiceFullKernel (q ^ h) d M p r ep (Universal.Choices.Construction.universalBlockChoice (q ^ h) d M p repr)
    ∃ R : F.Model,
    let AC := A.pullback (TotalParameters.Construction.totalParameterSource Z.space Q)
    ∃ f : IntrinsicFineTargetData.Construction.NativeFinePELTarget AC (q ^ h) Z,
      (∀ (U : Over (TotalParameters.Construction.totalParameter Z.space Q).left) (z : U ⟶ AC.polarized.abelian.scheme),
        z ≫ f.isogeny.hom = 1 ↔ ∃! w : U ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
          w ≫ Intrinsic.Stability.Construction.nativeSubgroupInclusion A.polarized.abelian Q F R = z) ∧
      (let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion AC.polarized.abelian.scheme (q ^ h))
          (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.isogeny.hom);
        (Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback Q.hom (Grp.mk A.polarized.abelian.scheme)
          (Grp.mk A.polarized.abelian.scheme) (q ^ h) b).relativeAnnihilator H = H) ∧
      ∀ (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)) (x : Over.mk c ⟶ Z.space),
        ∃ hfin : Finite (CorrespondenceFibers.Construction.SourceFiber (TotalParameters.Construction.totalParameterSource Z.space Q) x),
          @CorrespondenceFibers.Construction.correspondenceFiberMultiset _ _ _ _ _ (TotalParameters.Construction.totalParameterSource Z.space Q) f.target x hfin =
            Reference.HeckeTargets.Construction.originalRawHeckeMultiset Z hZ j arithmeticEmbedding hsplit hd hdegree h labels hlabels
              a ha hdominant hcop hpol h_FiniteDescent x

set_option backward.isDefEq.respectTransparency false in
theorem integral_hecke_family_exists :
    IntegralHeckeFamily Z hZ κ₀ hC j arithmeticEmbedding hsplit hd hdegree h labels hlabels
      a ha hdominant hcop hpol h_FiniteDescent := by
  let A := Z.universal
  let hA := FinePELUniversalFunctions.Construction.finePEL_universal_hasUniversalGlobalFunctions Z hZ κ₀ hC
  let hD := GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA
  let M := fun v => ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)
  let : ∀ v, Module (ZMod (q ^ h)) (M v) :=
    fun v => ElementaryModules.Construction.rankThreeElementaryModule_structure q h (a v) (ha v)
  let b := UniversalFunction.PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A.polarized.abelian A.polarized.dual
    A.polarized.polarization hD (q ^ h) (pow_pos (Fact.out : q.Prime).pos h)
  have hp : Nat.Coprime (q ^ h) ((∏ i, P.polarizationType i) ^ 2) := (hpol.pow_right 2).pow_left h
  obtain ⟨Q, hQf, hQe, repr, R, f, hker⟩ :=
    UniversalFunction.CanonicalCorrespondence.Construction.universalFunction_canonical_fine_correspondence A hA q hcop h hp j arithmeticEmbedding hsplit
      labels hlabels M h_FiniteDescent Z hZ
  refine ⟨Q, hQf, hQe, repr, TotalParameters.Construction.totalParameterIso Z.space Q _ repr,
    TotalParameters.Construction.totalParameterIso_forget Z.space Q _ repr, hQf, hQe, R, f, hker, ?_, ?_⟩
  · apply Intrinsic.Isotropy.Construction.nativeQuotient_kernel_self_annihilating A.polarized.abelian Q _ R f.isogeny hker (q ^ h) b
    apply CM.PointsPerfectKernel.Construction.l45_choice_kernel_self_annihilating_from_perfect_source j arithmeticEmbedding hsplit
      A.polarized.abelian A.action h d labels b Z.space.hom hlabels M _
    · exact UniversalFunction.PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing_isPerfect A.polarized.abelian A.polarized.dual
        A.polarized.polarization hD (q ^ h) (pow_pos (Fact.out : q.Prime).pos h) hp
    · exact UniversalFunction.PairingAlternation.Construction.universalFunctionNativePolarizationPairing_alternating A.polarized.dual hD
        A.polarized.polarization (q ^ h) (pow_pos (Fact.out : q.Prime).pos h) Z.space.hom
    · exact UniversalFunction.PairingAdjoints.Construction.universalFunctionNativePolarizationPairing_coefficient_adjoint A.polarized hD A.action A.rosati
        (q ^ h) (pow_pos (Fact.out : q.Prime).pos h)
  · intro c x
    let hfin := Relative.FiberEquiv.Construction.relativeParameterRawFiber_finite A x j arithmeticEmbedding hsplit h labels M
      hd hdegree a ha hdominant (fun _ => AddEquiv.ulift) Q repr
    refine ⟨hfin, ?_⟩
    exact UniversalFunction.ParameterMultiset.Construction.universalFunctionParameterFineTarget_multiset A hA x j arithmeticEmbedding hsplit h labels M
      hd hdegree a ha hdominant (fun _ => AddEquiv.ulift) Q repr hcop hp hlabels h_FiniteDescent Z hZ R f hker

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntegralHecke.Construction
