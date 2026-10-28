import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientDescentCompatibility
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.IdealDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfullyFlatIdealEquality
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Faithfully Flat Coefficient Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FaithfullyFlatCoefficientDescent

noncomputable section

/-! A coefficient ideal descends along a faithfully flat affine cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct

universe u
variable (R A : CommRingCat.{u}) [Algebra R A] [Module.FaithfullyFlat R A]
variable {X : Scheme.{u}} (f : X ⟶ Spec R) [Flat f] (K : X.IdealSheafData)

theorem affineIdealCoefficient_faithfullyFlat_descent (C : Ideal A)
    (hC : Affine.IdealCoefficientTests.IsAffineIdealCoefficient A
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A))))
      (K.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R A))))) C) :
    Affine.IdealCoefficientTests.IsAffineIdealCoefficient R f K (C.comap (algebraMap R A)) := by
  let φ : R ⟶ A := CommRingCat.ofHom (algebraMap R A)
  let a : A ⟶ CommRingCat.of (A ⊗[R] A) :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom
  let b : A ⟶ CommRingCat.of (A ⊗[R] A) :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom
  have hab : φ ≫ a = φ ≫ b := (CommRingCat.isPushout_tensorProduct R A A).w
  have hc := CoefficientDescentCompatibility.affineIdealCoefficient_descent_compatibility f K φ C hC a b hab
  have hdesc : (C.comap (algebraMap R A)).map (algebraMap R A) = C :=
    Presentations.Flat.IdealDescent.flat_ideal_descent R A C hc.le
  let g := Spec.map φ
  have hg : Flat g ∧ Surjective g :=
    (flat_and_surjective_SpecMap_iff φ).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let : Flat g := hg.1
  let : Surjective g := hg.2
  let p := pullback.fst f g
  let q := pullback.snd f g
  intro L
  have hbase : ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm L).comap g =
      (SpectrumIdealCoordinates.spectrumIdealCoordinates A).symm (L.map (algebraMap R A)) := by
    apply (SpectrumIdealCoordinates.spectrumIdealCoordinates A).injective
    rw [SpectrumIdealCoordinates.spectrumIdealCoordinates_comap, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
    rfl
  have hpull : (((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm L).comap f).comap p =
      ((SpectrumIdealCoordinates.spectrumIdealCoordinates A).symm (L.map (algebraMap R A))).comap q := by
    rw [← Scheme.IdealSheafData.comap_comp, pullback.condition,
      Scheme.IdealSheafData.comap_comp, hbase]
  constructor
  · intro h
    have hm := Scheme.IdealSheafData.comap_mono p h
    dsimp only at hm
    rw [hpull] at hm
    have hc := (hC _).mp hm
    rw [← hdesc] at hc
    have he := Ideal.comap_mono (f := algebraMap R A) hc
    simpa only [Ideal.comap_map_eq_self_of_faithfullyFlat] using he
  · intro h
    have hc : C ≤ L.map (algebraMap R A) := by
      rw [← hdesc]
      exact Ideal.map_mono h
    apply AbelianModuli.HilbertConstruction.FaithfullyFlatIdealEquality.ideal_le_of_faithfullyFlat p
    rw [hpull]
    exact (hC _).mpr hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FaithfullyFlatCoefficientDescent
