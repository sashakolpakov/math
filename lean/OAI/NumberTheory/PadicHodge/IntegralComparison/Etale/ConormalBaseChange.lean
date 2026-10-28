import Mathlib.RingTheory.Etale.Kaehler
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ConormalRank

/-! # Conormal Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConormalBaseChange

noncomputable section

/-! The actual cotangent-sequence maps commute with formally étale
base change. The ambient equivalence is the native extension map on
differentials, with its exact pure-tensor formula. -/

open scoped TensorProduct

open _root_.Algebra.Extension KaehlerDifferential

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (P : Algebra.Extension.{u} R S) (Q : Algebra.Extension.{u} R T) (f : P.Hom Q)

def ambient (hf : f.toRingHom.FormallyEtale) :
    T ⊗[S] P.CotangentSpace ≃ₗ[T] Q.CotangentSpace :=
  Algebra.Extension.tensorCotangentSpaceOfFormallyEtale f hf

theorem ambient_tmul (hf : f.toRingHom.FormallyEtale) (t : T) (x : P.CotangentSpace) :
    ambient P Q f hf (t ⊗ₜ[S] x) = t • CotangentSpace.map f x := by
  exact LinearMap.liftBaseChange_tmul T (CotangentSpace.map f) t x

theorem ambient_tmul_D (hf : f.toRingHom.FormallyEtale) (t : T) (s : S) (x : P.Ring) :
    ambient P Q f hf (t ⊗ₜ[S] (s ⊗ₜ[P.Ring] D R P.Ring x)) =
      (t * algebraMap S T s) ⊗ₜ[Q.Ring] D R Q.Ring (f.toRingHom x) := by
  rw [ambient_tmul, CotangentSpace.map_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  rfl

theorem ambient_cotangent (hf : f.toRingHom.FormallyEtale) (x : P.Cotangent) :
    ambient P Q f hf (1 ⊗ₜ[S] P.cotangentComplex x) =
      Q.cotangentComplex (Cotangent.map f x) := by
  rw [ambient_tmul, one_smul, CotangentSpace.map_cotangentComplex]

theorem toKaehler_map (x : P.CotangentSpace) :
    Q.toKaehler (CotangentSpace.map f x) =
      KaehlerDifferential.map R R S T (P.toKaehler x) := by
  let : Algebra P.Ring T := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  let : IsScalarTower P.Ring S T := IsScalarTower.of_algebraMap_eq' rfl
  have he : (Q.toKaehler.restrictScalars S).comp (CotangentSpace.map f) =
      (KaehlerDifferential.map R R S T).comp P.toKaehler := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s ω
    have hω : ω ∈ Submodule.span P.Ring (Set.range (D R P.Ring)) := by
      rw [span_range_derivation]
      trivial
    induction hω using Submodule.span_induction generalizing s with
    | mem ω hω =>
      obtain ⟨a, rfl⟩ := hω
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        CotangentSpace.map_tmul, Algebra.Extension.toKaehler,
        KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D,
        map_smul, Algebra.Extension.Hom.toAlgHom_apply, Algebra.Extension.Hom.algebraMap_toRingHom]
      exact algebraMap_smul T s _
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add x y hx hy ihx ihy => simp only [TensorProduct.tmul_add, map_add, ihx, ihy]
    | smul a ω hω ih => simpa only [TensorProduct.smul_tmul] using ih (a • s)
  exact LinearMap.congr_fun he x

theorem ambient_toKaehler (hf : f.toRingHom.FormallyEtale)
    [Algebra.FormallyEtale S T] (x : T ⊗[S] P.CotangentSpace) :
    Q.toKaehler (ambient P Q f hf x) =
      tensorKaehlerEquivOfFormallyEtale R S T (P.toKaehler.baseChange T x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul t x =>
    rw [ambient_tmul, map_smul, toKaehler_map, LinearMap.baseChange_tmul,
      tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConormalBaseChange
