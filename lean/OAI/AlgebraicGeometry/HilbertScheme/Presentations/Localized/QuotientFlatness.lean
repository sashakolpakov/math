import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReducedIdealTensorCriterion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.RingExtension
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Localization

/-! # Quotient Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.QuotientFlatness

noncomputable section

/-! Flatness of reduction and ideal-tensor injectivity pass to localizations
of the source algebra, giving the Noetherian local flatness criterion there. -/

open TensorProduct

universe u v w
variable (B : Type u) [CommRing B]
variable (S : Type v) [CommRing S] [Algebra B S]
variable (T : Type w) [CommRing T] [Algebra S T] [Algebra B T] [IsScalarTower B S T]

theorem localized_quotient_flat (U : Submonoid S) [IsLocalization U T]
    (I : Ideal B) [Module.Flat (B ⧸ I) (S ⧸ I.map (algebraMap B S))] :
    Module.Flat (B ⧸ I) (T ⧸ I.map (algebraMap B T)) := by
  let J := I.map (algebraMap B S)
  have he : J.map (algebraMap S T) = I.map (algebraMap B T) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let K := I.map (algebraMap B T)
  let : Algebra (S ⧸ J) (T ⧸ K) := Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp he.le)
  let : IsScalarTower (B ⧸ I) (S ⧸ J) (T ⧸ K) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk _ (algebraMap B T x) =
        Ideal.Quotient.mk _ (algebraMap S T (algebraMap B S x))
      rw [IsScalarTower.algebraMap_apply B S T])
  let : IsLocalization (Algebra.algebraMapSubmonoid (S ⧸ J) U) (T ⧸ K) :=
    IsLocalization.of_surjective U T (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective rfl (by
        simpa only [Ideal.mk_ker] using he.ge)
  have : Module.Flat (S ⧸ J) (T ⧸ K) :=
    IsLocalization.flat _ (Algebra.algebraMapSubmonoid (S ⧸ J) U)
  exact Module.Flat.trans (B ⧸ I) (S ⧸ J) _

theorem localized_flat_of_idealTensor_injective
    [IsNoetherianRing B] [IsLocalRing B]
    [IsNoetherianRing T] [IsLocalRing T] [IsLocalHom (algebraMap B T)]
    (U : Submonoid S) [IsLocalization U T]
    (I : Ideal B) (hI : I ≠ ⊤)
    [Module.Flat (B ⧸ I) (S ⧸ I.map (algebraMap B S))]
    (hinj : Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication B B S I)) :
    Module.Flat B T := by
  have : Module.Flat S T := IsLocalization.flat T U
  have : Module.Flat (B ⧸ I) (T ⧸ I.map (algebraMap B T)) :=
    localized_quotient_flat B S T U I
  have : Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] T) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T I).symm.toLinearEquiv
  exact ReducedIdealTensorCriterion.flat_of_idealTensor_injective_of_flat_reduction T I hI
    (IdealTensor.RingExtension.idealTensorMultiplication_ring_flat_extension S T I hinj)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.QuotientFlatness
