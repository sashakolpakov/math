import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConormalBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExteriorAdjunctionBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ConormalRank

/-! # Conormal Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConormalResidue

noncomputable section

/-! The native smooth cotangent residue commutes with an étale map of
extensions whose conormal module is the actual scalar extension. -/

open _root_.Module _root_.Algebra.Extension KaehlerDifferential
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConormalBaseChange OAI.NumberTheory.PadicHodge.IntegralComparison.SplitExteriorAdjunction

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (P : Algebra.Extension.{u} R S) (Q : Algebra.Extension.{u} R T) (f : P.Hom Q)
  [Algebra P.Ring Q.Ring] (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
  (hker : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring))
  (hf : f.toRingHom.FormallyEtale) [Algebra.FormallyEtale S T]
  [Algebra.Smooth R P.Ring] [Algebra.Smooth R S]
  [Algebra.Smooth R Q.Ring] [Algebra.Smooth R T]

abbrev conormal : T ⊗[S] P.Cotangent ≃ₗ[T] Q.Cotangent :=
  Algebra.Extension.tensorCotangent f halg hker

omit [IsScalarTower R S T] [Algebra.FormallyEtale S T]
  [Algebra.Smooth R P.Ring] [Algebra.Smooth R S]
  [Algebra.Smooth R Q.Ring] [Algebra.Smooth R T] in
theorem conormal_tmul (t : T) (x : P.Cotangent) :
    conormal P Q f halg hker (t ⊗ₜ[S] x) = t • Cotangent.map f x :=
  LinearMap.liftBaseChange_tmul T (Cotangent.map f) t x

abbrev sourceSplit := (IntegralComparison.Smooth.ConormalRank.differentialSplit P).symm
abbrev targetSplit := (IntegralComparison.Smooth.ConormalRank.differentialSplit Q).symm
abbrev baseSplit := ExteriorAdjunctionBaseChange.Split.splitting T (sourceSplit P)

omit [Algebra.FormallyEtale S T] in
theorem inclusion (x : T ⊗[S] P.Cotangent) :
    ConormalBaseChange.ambient P Q f hf (baseSplit P (x, 0)) =
      targetSplit Q (conormal P Q f halg hker x, 0) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    have hxy : (x + y, (0 : T ⊗[S] Ω[S⁄R])) = (x, 0) + (y, 0) := by simp
    rw [hxy, map_add, map_add, hx, hy, map_add]
    exact (map_add (targetSplit Q) _ _).symm
  | tmul t x =>
    rw [ExteriorAdjunctionBaseChange.Split.splitting_left_tmul,
      IntegralComparison.Smooth.ConormalRank.SplitNormalization.inl, ConormalBaseChange.ambient_tmul,
      CotangentSpace.map_cotangentComplex, conormal_tmul,
      IntegralComparison.Smooth.ConormalRank.SplitNormalization.inl, map_smul]

omit [Algebra P.Ring Q.Ring] in
theorem projection (x : T ⊗[S] P.CotangentSpace) :
    tensorKaehlerEquivOfFormallyEtale R S T ((baseSplit P).symm x).2 =
      ((targetSplit Q).symm (ConormalBaseChange.ambient P Q f hf x)).2 := by
  dsimp only [targetSplit, LinearEquiv.symm_symm]
  rw [IntegralComparison.Smooth.ConormalRank.SplitNormalization.snd, ConormalBaseChange.ambient_toKaehler]
  congr 1
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Prod.snd_add, hx, hy]
  | tmul t x =>
    rw [ExteriorAdjunctionBaseChange.Split.splitting_symm_tmul,
      LinearMap.baseChange_tmul]
    change t ⊗ₜ[S] (IntegralComparison.Smooth.ConormalRank.differentialSplit P x).2 = _
    rw [IntegralComparison.Smooth.ConormalRank.SplitNormalization.snd]

variable {c g : ℕ} (bI : Basis (Fin c) S P.Cotangent) (bQ : Basis (Fin g) S Ω[S⁄R])

def conormalBasis : Basis (Fin c) T Q.Cotangent :=
  (bI.baseChange T).map (conormal P Q f halg hker)

def quotientBasis : Basis (Fin g) T Ω[T⁄R] :=
  (bQ.baseChange T).map (tensorKaehlerEquivOfFormallyEtale R S T)

theorem residue_naturality :
    (SplitExteriorAdjunction.residue (conormalBasis P Q f halg hker bI) (quotientBasis bQ) (targetSplit Q)).toLinearMap.comp
      ((exteriorPower.map (c + g) (ConormalBaseChange.ambient P Q f hf).toLinearMap).comp
        (GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap S T P.CotangentSpace (c + g))) =
      ((exteriorPower.map g (tensorKaehlerEquivOfFormallyEtale R S T).toLinearMap).comp
        (GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap S T Ω[S⁄R] g)).comp
          ((SplitExteriorAdjunction.residue bI bQ (sourceSplit P)).toLinearMap.baseChange T) := by
  have h := ExteriorAdjunctionBaseChange.SplitNaturality.residue_naturality
    (bI.baseChange T) (bQ.baseChange T) (baseSplit P)
    (conormal P Q f halg hker) (tensorKaehlerEquivOfFormallyEtale R S T)
    (ConormalBaseChange.ambient P Q f hf) (targetSplit Q)
    (inclusion P Q f halg hker hf) (projection P Q f hf)
  dsimp only [conormalBasis, quotientBasis]
  rw [← LinearMap.comp_assoc, h, LinearMap.comp_assoc,
    ExteriorAdjunctionBaseChange.Split.residue_baseChange,
    ← LinearMap.comp_assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConormalResidue
