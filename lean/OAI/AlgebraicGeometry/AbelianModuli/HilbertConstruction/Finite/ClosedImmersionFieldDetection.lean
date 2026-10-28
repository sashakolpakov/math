import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AlgebraSurjectivityFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorIsoNaturality
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Closed Immersion Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ClosedImmersionFieldDetection

noncomputable section

/-! Closed immersion of a finite map between affine schemes over a spectrum
is detected by all field-valued base changes of that spectrum. -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem ringHom_surjective_of_SpecMap_closedImmersion {S T : CommRingCat.{u}} (φ : S ⟶ T)
    [IsClosedImmersion (Spec.map φ)] : Function.Surjective φ := by
  have h := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map φ)).2
  intro t
  obtain ⟨z, hz⟩ := h ((Scheme.ΓSpecIso T).inv t)
  refine ⟨(Scheme.ΓSpecIso S).hom z, ?_⟩
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality φ) z
  change (Scheme.ΓSpecIso T).hom ((Spec.map φ).appTop z) = φ ((Scheme.ΓSpecIso S).hom z) at hn
  rw [hz] at hn
  exact hn.symm.trans (ConcreteCategory.congr_hom (Scheme.ΓSpecIso T).inv_hom_id t)

theorem finite_affine_overMap_closedImmersion_of_field_baseChanges
    (R : Type u) [CommRing R] {X Y : Over (Spec (.of R))}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) [IsFinite f.left]
    (h : ∀ (K : Type u) [Field K] [Algebra R K],
      IsClosedImmersion (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f).left)) :
    IsClosedImmersion f.left := by
  let S := Affine.OverChartPoints.affineOverAlgebra R Y
  let T := Affine.OverChartPoints.affineOverAlgebra R X
  let φ : S →ₐ[R] T := Affine.OverMorphisms.affineOverMap R f
  let : Algebra S T := φ.toRingHom.toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun r => (φ.commutes r).symm)
  have hφ : IsFinite (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    have : IsIso (Affine.OverChartPoints.affineOverIso R X).inv.left := inferInstanceAs (IsIso ((Over.forget _).map (Affine.OverChartPoints.affineOverIso R X).inv))
    have : IsIso (Affine.OverChartPoints.affineOverIso R Y).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (Affine.OverChartPoints.affineOverIso R Y).hom))
    rw [Affine.OverMorphisms.affineOverMap_spec]
    infer_instance
  have : Module.Finite S T := (IsFinite.SpecMap_iff (CommRingCat.ofHom φ.toRingHom)).mp hφ
  have hs : Function.Surjective φ := AlgebraSurjectivityFieldDetection.finiteAlgebraMap_surjective_of_field_baseChanges R S T (by
    intro K _ _
    have : IsClosedImmersion (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f).left) := h K
    have : IsIso (Affine.TensorOverIso.affineTensorOverIso R K X).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (Affine.TensorOverIso.affineTensorOverIso R K X).hom))
    have : IsIso (Affine.TensorOverIso.affineTensorOverIso R K Y).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (Affine.TensorOverIso.affineTensorOverIso R K Y).hom))
    have hn : (Affine.TensorOverIso.affineTensorOverMap R K f).left ≫ (Affine.TensorOverIso.affineTensorOverIso R K Y).hom.left =
        (Affine.TensorOverIso.affineTensorOverIso R K X).hom.left ≫ ((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f).left :=
      congrArg Over.Hom.left (Affine.TensorIsoNaturality.affineTensorOverIso_natural (R := K) f)
    have ht : IsClosedImmersion
        ((Affine.TensorOverIso.affineTensorOverMap R K f).left ≫ (Affine.TensorOverIso.affineTensorOverIso R K Y).hom.left) := by
      rw [hn]
      infer_instance
    have : IsClosedImmersion (Affine.TensorOverIso.affineTensorOverMap R K f).left :=
      IsClosedImmersion.of_comp _ (Affine.TensorOverIso.affineTensorOverIso R K Y).hom.left
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id K K) φ).toRingHom)) :=
      inferInstanceAs (IsClosedImmersion (Affine.TensorOverIso.affineTensorOverMap R K f).left)
    exact ringHom_surjective_of_SpecMap_closedImmersion
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K) φ).toRingHom))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hs
  have : IsIso (Affine.OverChartPoints.affineOverIso R X).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (Affine.OverChartPoints.affineOverIso R X).hom))
  have : IsIso (Affine.OverChartPoints.affineOverIso R X).inv.left := inferInstanceAs (IsIso ((Over.forget _).map (Affine.OverChartPoints.affineOverIso R X).inv))
  have : IsIso (Affine.OverChartPoints.affineOverIso R Y).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (Affine.OverChartPoints.affineOverIso R Y).hom))
  have hc : IsClosedImmersion ((Affine.OverChartPoints.affineOverIso R X).inv.left ≫ f.left ≫
      (Affine.OverChartPoints.affineOverIso R Y).hom.left) := by
    rw [← Affine.OverMorphisms.affineOverMap_spec]
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))
    infer_instance
  have : IsClosedImmersion (((Affine.OverChartPoints.affineOverIso R X).inv.left ≫ f.left) ≫ (Affine.OverChartPoints.affineOverIso R Y).hom.left) := by
    simpa only [Category.assoc] using hc
  have : IsClosedImmersion ((Affine.OverChartPoints.affineOverIso R X).inv.left ≫ f.left) :=
    IsClosedImmersion.of_comp _ (Affine.OverChartPoints.affineOverIso R Y).hom.left
  have he : f.left = (Affine.OverChartPoints.affineOverIso R X).hom.left ≫ ((Affine.OverChartPoints.affineOverIso R X).inv.left ≫ f.left) := by
    have hi : (Affine.OverChartPoints.affineOverIso R X).hom.left ≫ (Affine.OverChartPoints.affineOverIso R X).inv.left = 𝟙 X.left :=
      congrArg Over.Hom.left (Affine.OverChartPoints.affineOverIso R X).hom_inv_id
    simp only [← Category.assoc, hi, Category.id_comp]
  rw [he]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ClosedImmersionFieldDetection
