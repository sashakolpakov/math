import OAI.NumberTheory.Quaternion.Arithmetic.OrbitTopology
import OAI.NumberTheory.Quaternion.Arithmetic.CompactRestrictedBoxes
import OAI.NumberTheory.Quaternion.Arithmetic.IntegralCompact

/-! # Finite Orbit Compact -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteOrbitCompact

noncomputable section

/-! Requiring the finite-place images of a fixed rational quaternion
unit to be integral defines a compact set of finite-adelic points. -/

open scoped Classical _root_.NumberField _root_.Quaternion _root_.Matrix
open QuaternionAlgebra IsDedekindDomain Set Filter

variable {F : Type} [Field F] [NumberField F]

def quaternionScalarUnit {K : Type} [Field K] (ρ : F →+* K) (a b : F)
    (r : ℍ[F,a,b]ˣ) : ℍ[K,ρ a,ρ b]ˣ :=
  Units.map (ConjugationQuaternion.quaternionCoefficientMap ρ a b).toMonoidHom r

def quaternionFiniteOrbitBox (a b : F) (r : ℍ[F,a,b]ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    Set (LocalAdeles.LocalPoints (MatrixGroup.quaternionNormOneMatrixGroup a b) (.inr v)) :=
  {g | ∀ i, OrbitTopology.quaternionPointsOrbit a b (LocalAdeles.localEmbedding (.inr v))
    (quaternionScalarUnit (LocalAdeles.localEmbedding (.inr v)) a b r) g i ∈ LocalAdeles.localIntegerRing (.inr v)}

theorem quaternionFiniteOrbitBox_isCompact (a b : F) (r : ℍ[F,a,b]ˣ)
    (v : HeightOneSpectrum (𝓞 F)) : IsCompact (quaternionFiniteOrbitBox a b r v) := by
  have hC : IsCompact {x : Fin 4 → LocalAdeles.Completion (.inr v) | ∀ i, x i ∈ LocalAdeles.localIntegerRing (.inr v)} := by
    have hc := isCompact_univ_pi (fun _ : Fin 4 => IntegralCompact.finiteLocalIntegerRing_isCompact v)
    simp only [Set.pi, mem_univ, forall_const] at hc
    exact hc
  exact OrbitTopology.quaternionPointsOrbit_compact_preimage a b (LocalAdeles.localEmbedding (.inr v))
    (quaternionScalarUnit (LocalAdeles.localEmbedding (.inr v)) a b r) _ hC

theorem eventually_quaternionFiniteOrbitBox_integral (a b : F) (r : ℍ[F,a,b]ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      quaternionFiniteOrbitBox a b r v ⊆ LocalAdeles.integralLocalSubgroup (MatrixGroup.quaternionNormOneMatrixGroup a b) (.inr v) := by
  have hall : ∀ᶠ v : LocalAdeles.Place F in cofinite,
      ∀ g : LocalAdeles.LocalPoints (MatrixGroup.quaternionNormOneMatrixGroup a b) v,
        (∀ i, OrbitTopology.quaternionPointsOrbit a b (LocalAdeles.localEmbedding v)
          (quaternionScalarUnit (LocalAdeles.localEmbedding v) a b r) g i ∈ LocalAdeles.localIntegerRing v) →
          g ∈ LocalAdeles.integralLocalSubgroup (MatrixGroup.quaternionNormOneMatrixGroup a b) v := by
    filter_upwards [LocalAdeles.eventually_integral_scalar a, LocalAdeles.eventually_integral_scalar b,
      LocalAdeles.eventually_integral_scalar (r⁻¹).val.re, LocalAdeles.eventually_integral_scalar (r⁻¹).val.imI,
      LocalAdeles.eventually_integral_scalar (r⁻¹).val.imJ, LocalAdeles.eventually_integral_scalar (r⁻¹).val.imK]
      with v ha hb h0 h1 h2 h3
    intro g hg
    exact OrbitReconstruction.quaternion_integral_of_integral_orbit a b (LocalAdeles.localEmbedding v) (LocalAdeles.localIntegerRing v)
      ha hb (quaternionScalarUnit (LocalAdeles.localEmbedding v) a b r) ⟨h0, h1, h2, h3⟩ g hg
  exact (show Function.Injective (Sum.inr : HeightOneSpectrum (𝓞 F) → LocalAdeles.Place F) from
    Sum.inr_injective).tendsto_cofinite hall

theorem quaternion_finite_integral_orbit_isCompact (a b : F) (r : ℍ[F,a,b]ˣ) :
    IsCompact {g : FiniteAdelicMatrices.FiniteAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b) |
      ∀ v, g v ∈ quaternionFiniteOrbitBox a b r v} :=
  CompactRestrictedBoxes.isCompact_restricted_product_box _ _ _ (quaternionFiniteOrbitBox_isCompact a b r)
    (eventually_quaternionFiniteOrbitBox_integral a b r)

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteOrbitCompact
