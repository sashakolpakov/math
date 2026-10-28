import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.AffineOpenCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TensorPullbackCoefficients
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NoetherianFlatFamilyFree
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.CoefficientOpenCover
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Generic Source Ideal Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GenericSourceIdealCoefficients

noncomputable section

/-! All ideals on a flat finite-type source over a Noetherian base have
coefficient ideals after restriction to one nonempty principal open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct

universe u
variable (R : CommRingCat.{u}) [IsNoetherianRing R] [Nontrivial R]
variable {X : Scheme.{u}} [CompactSpace X] (f : X ⟶ Spec R)
variable [Flat f] [LocallyOfFiniteType f]

theorem exists_generic_source_ideal_coefficients :
    ∃ s : R, ¬ IsNilpotent s ∧
      ∀ K : (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away s))))).IdealSheafData,
        ∃ I : Ideal (Localization.Away s),
          Affine.IdealCoefficientTests.IsAffineIdealCoefficient (CommRingCat.of (Localization.Away s))
            (pullback.snd f (Spec.map (CommRingCat.ofHom
              (algebraMap R (Localization.Away s))))) K I := by
  classical
  let U := Finite.AffineOpenCover.finiteAffineOpenCover X
  let ρ (i : U.I₀) : R ⟶ U.X i := Spec.preimage (U.f i ≫ f)
  let : ∀ i, Algebra R (U.X i) := fun i => (ρ i).hom.toAlgebra
  have hρ (i : U.I₀) : Spec.map (CommRingCat.ofHom (algebraMap R (U.X i))) = U.f i ≫ f :=
    Spec.map_preimage _
  let : ∀ i, Module.Flat R (U.X i) := fun i => by
    have hf : Flat (Spec.map (ρ i)) := by rw [Spec.map_preimage]; infer_instance
    exact Flat.SpecMap_iff.mp hf
  let : ∀ i, Algebra.FiniteType R (U.X i) := fun i => by
    have hf : LocallyOfFiniteType (Spec.map (ρ i)) := by rw [Spec.map_preimage]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hf
  obtain ⟨s, hs, hfree⟩ := NoetherianFlatFamilyFree.exists_generic_free_noetherian_flat_algebra_family R (fun i => U.X i)
  refine ⟨s, hs, ?_⟩
  intro K
  let A := CommRingCat.of (Localization.Away s)
  let g := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let V := Scheme.Pullback.openCoverOfLeft U.openCover f g
  have hcoeff (i : U.I₀) : ∃ I : Ideal A,
      Affine.IdealCoefficientTests.IsAffineIdealCoefficient A (V.f i ≫ pullback.snd f g) (K.comap (V.f i)) I := by
    let : Module.Free A (A ⊗[R] U.X i) := hfree i
    have hv : V.f i ≫ pullback.snd f g = pullback.snd (U.f i ≫ f) g := by
      change pullback.map (U.f i ≫ f) g f g (U.f i) (𝟙 _) (𝟙 _)
        (by simp) (by simp) ≫ pullback.snd f g = _
      simp only [pullback.map, pullback.lift_snd, Category.comp_id]
    rw [hv]
    exact Projective.TensorPullbackCoefficients.projective_tensor_pullback_coefficients_of_eq R A (U.X i) (U.f i ≫ f) (hρ i) _
  choose I hI using hcoeff
  exact ⟨⨆ i, I i, Affine.CoefficientOpenCover.affineIdealCoefficient_of_openCover A (pullback.snd f g) K V I hI⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GenericSourceIdealCoefficients
