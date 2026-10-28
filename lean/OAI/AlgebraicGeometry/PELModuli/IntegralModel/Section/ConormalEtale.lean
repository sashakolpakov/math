import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalMaps
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Conormal Etale -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalEtale.SectionConormal

noncomputable section

/-! Restricting a smooth section through an étale ambient morphism
induces an isomorphism of the actual conormal modules. -/

open scoped TensorProduct
open TensorProduct

variable (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
  [Algebra B R] [Algebra C R] [IsScalarTower R B R] [IsScalarTower R C R]
  [IsScalarTower B C R] [Algebra.FormallySmooth R B] [Algebra.FormallySmooth R C]
  [Algebra.FormallyEtale B C]

def etaleEquiv : (RingHom.ker (algebraMap B R)).Cotangent ≃ₗ[R]
    (RingHom.ker (algebraMap C R)).Cotangent :=
  (Divisors.LineBundles.Smooth.SectionCotangent.BundleCycles.smoothSectionCotangentEquiv R B).trans
    ((AlgebraTensorModule.cancelBaseChange B C R R (KaehlerDifferential R B)).symm.trans
      ((LinearEquiv.baseChange C R _ _
          (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B C)).trans
        (Divisors.LineBundles.Smooth.SectionCotangent.BundleCycles.smoothSectionCotangentEquiv R C).symm))

theorem etaleEquiv_toCotangent (b : RingHom.ker (algebraMap B R)) :
    etaleEquiv R B C (Ideal.toCotangent _ b) =
      Ideal.toCotangent _ ⟨algebraMap B C b,
        by rw [RingHom.mem_ker, ← IsScalarTower.algebraMap_apply B C R]; exact b.property⟩ := by
  apply (Divisors.LineBundles.Smooth.SectionCotangent.BundleCycles.smoothSectionCotangentEquiv R C).injective
  simp only [etaleEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Divisors.LineBundles.Smooth.SectionCotangent.BundleCycles.smoothSectionCotangentEquiv_toCotangent,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

theorem etaleEquiv_eq_map : (etaleEquiv R B C).toLinearMap =
    Ideal.mapCotangent (RingHom.ker (algebraMap B R)) (RingHom.ker (algebraMap C R))
      (IsScalarTower.toAlgHom R B C)
      (fun b hb => by
        change algebraMap C R (algebraMap B C b) = 0
        rw [← IsScalarTower.algebraMap_apply B C R]
        exact hb) := by
  apply LinearMap.ext
  intro v
  obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker (algebraMap B R)) v
  exact etaleEquiv_toCotangent R B C b

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalEtale.SectionConormal
