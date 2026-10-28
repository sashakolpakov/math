import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FlatIdealCoefficients
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentParameterRepresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.FactorizationCriterion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine Parameter Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AffineParameterLocus

noncomputable section

/-! An ideal on a proper flat source defines an actual closed parameter
locus over a Noetherian affine parameter base, on all test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem spectrum_morphism_quasiCompact {R A : CommRingCat.{u}} (g : Spec A ⟶ Spec R) :
    QuasiCompact g := inferInstance

variable {S : Scheme.{u}} (X : Over S) [Flat X.hom] [IsProper X.hom]
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (a : Spec R ⟶ S)

theorem proper_affine_parameter_locus (K : (Hilbert.Functor.ambient X (Over.mk a)).IdealSheafData) :
    ∃ (Z : Over S) (j : Z ⟶ Over.mk a), IsClosedImmersion j.left ∧
      (∀ (T : Over S) (x : T ⟶ Over.mk a), K.comap (Hilbert.Functor.ambientMap X x) = ⊥ ↔
        ∃! y : T ⟶ Z, y ≫ j = x) ∧
      ∃ e : yoneda.obj Z ≅ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X K ⊥).toFunctor,
        e.hom ≫ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X K ⊥).ι = yoneda.map j := by
  let f := Hilbert.Functor.ambientProjection X (Over.mk a)
  let : Flat f := by
    change Flat (prod.fst : Over.mk a ⨯ X ⟶ Over.mk a).left
    rw [← Over.prodLeftIsoPullback_hom_fst]
    infer_instance
  let : IsProper f := by
    change IsProper (prod.fst : Over.mk a ⨯ X ⟶ Over.mk a).left
    rw [← Over.prodLeftIsoPullback_hom_fst]
    infer_instance
  obtain ⟨I, hI⟩ := FlatIdealCoefficients.proper_flat_ideal_coefficients R _ f K
  let J := (SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm I
  let Z : Over S := Over.mk (J.subschemeι ≫ a)
  let j : Z ⟶ Over.mk a := Over.homMk J.subschemeι rfl
  let : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion J.subschemeι)
  have hspec : ∀ (A : Type u) [CommRing A] (b : Spec (CommRingCat.of A) ⟶ S)
      (x : Over.mk b ⟶ Over.mk a),
      x ∈ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X K ⊥).obj (.op (Over.mk b)) ↔
        ∃ y : Over.mk b ⟶ Z, y ≫ j = x := by
    intro A _ b x
    let : QuasiCompact x.left := spectrum_morphism_quasiCompact
      (R := R) (A := CommRingCat.of A) x.left
    let hp := (Hilbert.Functor.ambient_isPullback X x).flip
    have hk : (Hilbert.Functor.ambientMap X x).ker = x.left.ker.comap f := by
      rw [← hp.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso, KernelFlatBaseChange.kernel_flat_baseChange]
    have hzero : K.comap (Hilbert.Functor.ambientMap X x) = ⊥ ↔ J.comap x.left = ⊥ := by
      rw [AbelianModuli.HilbertConstruction.FaithfullyFlatIdealEquality.ideal_comap_eq_bot_iff_le_ker,
        AbelianModuli.HilbertConstruction.FaithfullyFlatIdealEquality.ideal_comap_eq_bot_iff_le_ker, hk]
      have he : x.left.ker = (SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm
          (SpectrumIdealCoordinates.spectrumIdealCoordinates R x.left.ker) :=
        ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm_apply_apply _).symm
      conv_lhs => rw [he]
      rw [hI]
      exact ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm.le_iff_le).symm.trans
        (by rw [(SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm_apply_apply])
    change K.comap (Hilbert.Functor.ambientMap X x) ≤ (⊥ : (Hilbert.Functor.ambient X (Over.mk a)).IdealSheafData).comap
      (Hilbert.Functor.ambientMap X x) ↔ _
    rw [Scheme.IdealSheafData.comap_bot, le_bot_iff, hzero]
    have hj : j.left.ker = J := J.ker_subschemeι
    rw [← hj, ← Closed.FactorizationCriterion.over_closed_factorization_iff_comap_bot j x]
    constructor
    · exact ExistsUnique.exists
    · rintro ⟨y, hy⟩
      let : Mono j := Over.mono_of_mono_left j
      exact ⟨y, hy, fun z hz => (cancel_mono j).mp (hz.trans hy.symm)⟩
  refine ⟨Z, j, inferInstanceAs (IsClosedImmersion J.subschemeι), ?_,
    Ideal.ContainmentParameterRepresentation.Hilbert.idealContainmentParameter_representation X K ⊥ j hspec⟩
  intro T x
  have h := Ideal.ContainmentParameterRepresentation.Hilbert.idealContainmentParameter_lifts X K ⊥ j hspec T x
  change K.comap (Hilbert.Functor.ambientMap X x) ≤
    (⊥ : (Hilbert.Functor.ambient X (Over.mk a)).IdealSheafData).comap (Hilbert.Functor.ambientMap X x) ↔ _ at h
  simpa only [Scheme.IdealSheafData.comap_bot, le_bot_iff] using h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AffineParameterLocus
