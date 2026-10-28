import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionDifferentials
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.Generators

/-! # Section Coordinates -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionCoordinates.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual étale kernel coordinates generate the section ideal -/

open KaehlerDifferential TensorProduct

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] [Algebra.FormallySmooth A B] {ι : Type}

def sectionCoordinateConormalBasis (b : Module.Basis ι B Ω[B⁄A]) :
    Module.Basis ι A (RingHom.ker (algebraMap B A)).Cotangent :=
  (b.baseChange A).map (SectionCotangent.BundleCycles.smoothSectionCotangentEquiv A B).symm

theorem sectionCoordinateConormalBasis_apply (v : ι → RingHom.ker (algebraMap B A))
    (b : Module.Basis ι B Ω[B⁄A]) (hb : ∀ i, b i = D A B (v i).val) (i : ι) :
    sectionCoordinateConormalBasis A B b i = Ideal.toCotangent _ (v i) := by
  apply (SectionCotangent.BundleCycles.smoothSectionCotangentEquiv A B).injective
  change SectionCotangent.BundleCycles.smoothSectionCotangentEquiv A B ((b.baseChange A).map (SectionCotangent.BundleCycles.smoothSectionCotangentEquiv A B).symm i) = _
  rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Module.Basis.baseChange_apply,
    hb i, SectionCotangent.BundleCycles.smoothSectionCotangentEquiv_toCotangent]

variable [IsLocalRing B] [IsNoetherianRing B] [Nontrivial A]

theorem sectionCoordinates_generate (v : ι → RingHom.ker (algebraMap B A))
    (b : Module.Basis ι B Ω[B⁄A]) (hb : ∀ i, b i = D A B (v i).val) :
    Ideal.span (Set.range (fun i => (v i).val)) = RingHom.ker (algebraMap B A) := by
  let I := RingHom.ker (algebraMap B A)
  have hI : I ≤ Ideal.jacobson (⊥ : Ideal B) :=
    (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (algebraMap B A))).trans
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal B) bot_ne_top).symm.le
  apply Conormal.Generators.BundleCycles.idealCotangent_lifts_generate I hI v
  have he : (fun i => I.toCotangent (v i)) = sectionCoordinateConormalBasis A B b :=
    funext fun i => (sectionCoordinateConormalBasis_apply A B v b hb i).symm
  rw [he]
  apply (Submodule.restrictScalars_eq_top_iff A B I.Cotangent).mp
  apply top_unique
  have h := Submodule.span_le_restrictScalars A B (Set.range (sectionCoordinateConormalBasis A B b))
  rw [(sectionCoordinateConormalBasis A B b).span_eq] at h
  exact h

theorem smoothSection_exists_generating_etaleCoordinates [Algebra.EssFiniteType A B] :
    ∃ (ι : Type) (_ : Finite ι) (v : ι → RingHom.ker (algebraMap B A)),
      Ideal.span (Set.range (fun i => (v i).val)) = RingHom.ker (algebraMap B A) ∧
        letI := DifferentialCoordinates.BundleCycles.differentialCoordinateAlgebra (R := A) (fun i => (v i).val)
        Algebra.FormallyEtale (MvPolynomial ι A) B := by
  obtain ⟨ι, hι, v, b, hb⟩ := SectionDifferentials.BundleCycles.smoothSection_exists_differentialBasis A B
  exact ⟨ι, hι, v, sectionCoordinates_generate A B v b hb,
    DifferentialCoordinates.BundleCycles.differentialCoordinate_formallyEtale (fun i => (v i).val) b hb⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionCoordinates.BundleCycles
