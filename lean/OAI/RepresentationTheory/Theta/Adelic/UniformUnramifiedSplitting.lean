import OAI.RepresentationTheory.Theta.Adelic.AllIntegralVacuum

/-! # Uniform Unramified Splitting -/

namespace OAI.RepresentationTheory.Theta.Adelic.UniformUnramifiedSplitting

noncomputable section

/-! Every family with the actual corrected unitary normalization is
uniformly unramified. This derives the missing adelic assembly condition
from character continuity, rational frames, and the exact local formula. -/

open Filter
open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.GlobalFrameIntegral OAI.RepresentationTheory.Theta.Adelic.IntegralTensor.PairAction OAI.RepresentationTheory.Theta.Adelic.IntegralScalarFamily.Family
open OAI.RepresentationTheory.Theta.Adelic.UnramifiedPlace.Data OAI.RepresentationTheory.Theta.Adelic.AllIntegralVacuum

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d) (n m : ℕ)
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
variable (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K)

include hH in
theorem localized_hermitian (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H v).val.conjTranspose = (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H v).val := by
  change (H.val.map (Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v)).conjTranspose = H.val.map (Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v)
  rw [← Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose (Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v) (Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_star (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v) d), hH]

include hK in
theorem localized_skew (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K v).val.conjTranspose = -(Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K v).val := by
  change (K.val.map (Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v)).conjTranspose = -(K.val.map (Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v))
  rw [← Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose (Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v) (Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_star (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v) d), hK]
  apply Matrix.ext
  intro i j
  exact (Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v).map_neg (K.val i j)

variable (s : ∀ v, (Weil.AdelicSplitting.Integral.Construction.LocalUnitary F H.val v × Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val v) →ₜ* Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (n * m) C.ψ v)
variable (hcovers : ∀ v g, Weil.AdelicSplitting.Vacuum.Construction.projectionAt F (n * m) C.ψ v (s v g) = Weil.AdelicSplitting.Assembly.Construction.localDualAction F d n m H K P v g)
variable (hnorm : ∀ v, Weil.AdelicSplitting.CorrectedNormalization.Construction.CorrectedLocalNormalization F d hd n m C v
  (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H v) (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K v) (P.localFrame v) (s v))

include hns hH hK hcovers hnorm in
theorem normalized_family_unramified : ∀ᶠ v in cofinite,
    Set.MapsTo (s v) (Weil.AdelicSplitting.Integral.Construction.localPairIntegral F H.val K.val v) (Weil.AdelicSplitting.Vacuum.Construction.coverIntegral F (n * m) C.ψ v) := by
  have ht : Tendsto (Sum.inr : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
      cofinite cofinite := Sum.inr_injective.tendsto_cofinite
  have hf : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in cofinite,
      Set.MapsTo (s (.inr v)) (Weil.AdelicSplitting.Integral.Construction.localPairIntegral F H.val K.val (.inr v))
        (Weil.AdelicSplitting.Vacuum.Construction.coverIntegral F (n * m) C.ψ (.inr v)) := by
    filter_upwards [UnramifiedPlace.Data.unramifiedPlaceData_eventually F d n m C hd,
      ht.eventually (GlobalFrameIntegral.integralFrameAt_eventually F d n m H K P),
      ht.eventually (IntegralScalarFamily.Family.integralScalarFamilyAt_eventually F d hns (2 * (n + m) + 1)),
      ht.eventually (IntegralTensor.PairAction.localizedUnit_integral_eventually F d H),
      ht.eventually (IntegralTensor.PairAction.localizedUnit_integral_eventually F d K)] with v hv hP hz hHI hKI
    intro g hg
    constructor
    · change Weil.AdelicSplitting.Vacuum.Construction.projectionAt F (n * m) C.ψ (.inr v) (s (.inr v) g) ∈ Weil.AdelicSplitting.Vacuum.Construction.symplecticIntegral F (n * m) (.inr v)
      rw [hcovers]
      exact IntegralTensor.PairAction.localDualAction_integral F d n m H K P (.inr v) hP hg
    · exact AllIntegralVacuum.integral_pair_fixes_vacuum F d hd hns n m H K P C v hv hP hz
        (localized_hermitian F d n H hH (.inr v)) (localized_skew F d m K hK (.inr v))
        hHI.1 hHI.2 hKI.1 hKI.2 (s (.inr v)) (hnorm (.inr v)) g hg
  filter_upwards [Weil.AdelicSplitting.UnramifiedCharacter.Construction.eventually_cofinite_sum_right (I := NumberField.InfinitePlace F) _ hf] with v hv
  cases v with
  | inr v => exact hv
  | inl v =>
    intro g _
    exact ⟨⟨fun _ _ => Subring.mem_top _, fun _ _ => Subring.mem_top _⟩, trivial⟩

end

end OAI.RepresentationTheory.Theta.Adelic.UniformUnramifiedSplitting
