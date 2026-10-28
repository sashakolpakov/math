import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexQuadratic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexLinear
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexFourier
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexNormalization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.WeilData
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.OscillatorReindex
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CoverFields

/-! # Weil Reindex Bare -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexBare.CM.Data

/-! Full Weil data on an arbitrary finite coordinate type, with every field
transported through the actual coordinate maps and measures. -/

open scoped Classical
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

def reindex (e : I ≃ J) (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData J MpR MpF MpA) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA where
  character := W.character
  character_continuous := W.character_continuous
  character_unitary := W.character_unitary
  character_rational := W.character_rational
  character_real := W.character_real
  finiteCharacter := W.finiteCharacter
  finiteCharacter_eq := W.finiteCharacter_eq
  finiteMeasure := ReindexMeasure.CM.finiteMeasure e W.finiteMeasure
  finiteMeasure_haar := by
    let := W.finiteMeasure_haar
    infer_instance
  finiteMeasure_selfDual := FourierReindex.CM.finite_selfDual e W.finiteCharacter W.finiteMeasure W.finiteMeasure_selfDual
  real := WeilReindexCovers.CM.real e W
  finite := WeilReindexCovers.CM.finite e W
  adelic := WeilReindexCovers.CM.adelic e W
  includeReal := W.includeReal
  includeFinite := W.includeFinite
  commute := W.commute
  factorization := WeilReindexCovers.CM.Product.factorization e W
  includeReal_covers := WeilReindexCovers.CM.Product.includeReal_covers e W
  includeFinite_covers := WeilReindexCovers.CM.Product.includeFinite_covers e W
  centralProduct_kernel := W.centralProduct_kernel
  decompose := WeilReindexCovers.CM.Product.decompose e W
  rationalSplit := WeilReindexCovers.CM.Product.rationalSplit e W
  rationalSplit_covers := WeilReindexCovers.CM.Product.rationalSplit_covers e W
  rational_linear := WeilReindexLinear.CM.rational_linear e W
  rational_quadratic := WeilReindexQuadratic.CM.rational_quadratic e W
  rational_fourier := WeilReindexFourier.CM.rational_fourier e W
  vacuum := WeilReindexNormalization.CM.vacuum e W
  vacuum_eq := WeilReindexNormalization.CM.vacuum_eq e W
  real_normalization := WeilReindexNormalization.CM.real_normalization e W

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM in
def weilData (I : Type*) [Fintype I] [DecidableEq I] :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I (Constructed.ConstructedAdelicGroup.CM.RealGroup (Fintype.card I)) (Constructed.ConstructedAdelicGroup.CM.FiniteGroup (Fintype.card I)) (Constructed.ConstructedAdelicGroup.CM.AdelicGroup (Fintype.card I)) :=
  reindex (Fintype.equivFin I) (Constructed.WeilData.CM.weilData (Fintype.card I))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexBare.CM.Data

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexBare.CM

/-! The intrinsic metaplectic group on an arbitrary source index maps
to the finite group of the fully constructed Weil data, with exact action. -/

open scoped Classical

variable (I : Type*) [Fintype I] [DecidableEq I]

def lift : Finite.BareNe.CM.Group.BareGroup (I := I) →*
    Constructed.ConstructedAdelicGroup.CM.FiniteGroup (Fintype.card I) :=
  Finite.OscillatorReindex.CM.bareReindex (Fintype.equivFin I)

theorem action (g : Finite.BareNe.CM.Group.BareGroup (I := I)) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    (Data.weilData I).finite.action (lift I g) φ = Finite.BareNe.CM.Group.bareAction g φ := by
  change (Finite.ReindexHeisenberg.CM.Pairing.testEquiv (Fintype.equivFin I)).symm
    ((Finite.ConstructedCover.CM.finiteCover (Fin (Fintype.card I))).action
      (lift I g) (Finite.ReindexHeisenberg.CM.Pairing.testEquiv (Fintype.equivFin I) φ)) = _
  rw [Finite.CoverFields.CM.action]
  change (Finite.ReindexHeisenberg.CM.Pairing.testEquiv (Fintype.equivFin I)).symm
    (Finite.FiniteOscillator.CM.action (Finite.OscillatorReindex.CM.reindex (Fintype.equivFin I) g.val)
      (Finite.ReindexHeisenberg.CM.Pairing.testEquiv (Fintype.equivFin I) φ)) = _
  rw [Finite.OscillatorReindex.CM.action_reindex, LinearEquiv.symm_apply_apply]
  rfl

theorem projection_matrix (g : Finite.BareNe.CM.Group.BareGroup (I := I)) :
    ((Data.weilData I).finite.project (lift I g)).val =
      (Finite.BareNe.CM.Group.bareProjection g).val := by
  change (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex (Fintype.equivFin I).symm
    ((Finite.ConstructedCover.CM.finiteCover (Fin (Fintype.card I))).project (lift I g))).val = _
  apply Matrix.ext
  intro i j
  change ((Finite.ConstructedCover.CM.finiteCover (Fin (Fintype.card I))).project (lift I g)).val
    (((Fintype.equivFin I).sumCongr (Fintype.equivFin I)) i)
    (((Fintype.equivFin I).sumCongr (Fintype.equivFin I)) j) = _
  rw [Finite.CoverFields.CM.projection_matrix]
  change (Finite.BareNe.CM.Group.bareProjection g).val
    (((Fintype.equivFin I).sumCongr (Fintype.equivFin I)).symm
      (((Fintype.equivFin I).sumCongr (Fintype.equivFin I)) i))
    (((Fintype.equivFin I).sumCongr (Fintype.equivFin I)).symm
      (((Fintype.equivFin I).sumCongr (Fintype.equivFin I)) j)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexBare.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexBare.CM.FiniteOscillator

/-! Every element of the constructed source finite Weil group is an
actual unitary oscillator on the source index, with the same projection. -/

open scoped Classical _root_.Matrix

variable (I : Type*) [Fintype I] [DecidableEq I]

def oscillator : Constructed.ConstructedAdelicGroup.CM.FiniteGroup (Fintype.card I) →*
    Finite.FiniteOscillator.CM.Oscillator (I := I) :=
  (Finite.OscillatorReindex.CM.reindex (Fintype.equivFin I).symm).comp
    Finite.BareNe.CM.Group.bareSubgroup.subtype

theorem action (g : Constructed.ConstructedAdelicGroup.CM.FiniteGroup (Fintype.card I))
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : Finite.FiniteOscillator.CM.action (oscillator I g) φ =
      (Data.weilData I).finite.action g φ := by
  change Finite.ReindexHeisenberg.CM.Pairing.testEquiv (Fintype.equivFin I).symm
    (Finite.BareNe.CM.Group.bareAction g
      ((Finite.ReindexHeisenberg.CM.Pairing.testEquiv (Fintype.equivFin I).symm).symm φ)) =
    (Finite.ReindexHeisenberg.CM.Pairing.testEquiv (Fintype.equivFin I)).symm
      ((Finite.ConstructedCover.CM.finiteCover (Fin (Fintype.card I))).action g
        (Finite.ReindexHeisenberg.CM.Pairing.testEquiv (Fintype.equivFin I) φ))
  rw [Finite.CoverFields.CM.action]
  rfl

theorem projection_matrix (g : Constructed.ConstructedAdelicGroup.CM.FiniteGroup (Fintype.card I)) :
    (Finite.FiniteOscillator.CM.projection (oscillator I g)).val =
      ((Data.weilData I).finite.project g).val := by
  apply Matrix.ext
  intro i j
  exact (congrFun (congrFun (Finite.CoverFields.CM.projection_matrix (Fin (Fintype.card I)) g)
    (((Fintype.equivFin I).sumCongr (Fintype.equivFin I)) i))
      (((Fintype.equivFin I).sumCongr (Fintype.equivFin I)) j)).symm

theorem unitary (g : Constructed.ConstructedAdelicGroup.CM.FiniteGroup (Fintype.card I))
    (φ ψ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    Finite.FiniteOscillator.CM.integralPairing ((Data.weilData I).finite.action g φ)
      ((Data.weilData I).finite.action g ψ) = Finite.FiniteOscillator.CM.integralPairing φ ψ := by
  rw [← FiniteOscillator.action I g φ, ← FiniteOscillator.action I g ψ]
  exact Finite.FiniteOscillator.CM.unitary (oscillator I g) φ ψ

theorem covariance (g : Constructed.ConstructedAdelicGroup.CM.FiniteGroup (Fintype.card I))
    (v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    (Data.weilData I).finite.action g
        (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) φ) =
      Finite.FourierHeisenberg.CM.operator
        (fun i => (((Data.weilData I).finite.project g).val *ᵥ v) (.inl i))
        (fun i => (((Data.weilData I).finite.project g).val *ᵥ v) (.inr i))
        ((Data.weilData I).finite.action g φ) := by
  have h := (oscillator I g).property.2 v φ
    (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) φ)
  have hh := h.mp rfl
  apply Subtype.ext
  change (Finite.FiniteOscillator.CM.action (oscillator I g) _).val =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character
      (fun i => ((Finite.FiniteOscillator.CM.projection (oscillator I g)).val *ᵥ v) (.inl i))
      (fun i => ((Finite.FiniteOscillator.CM.projection (oscillator I g)).val *ᵥ v) (.inr i))
      (Finite.FiniteOscillator.CM.action (oscillator I g) φ).val at hh
  rw [FiniteOscillator.action I g, projection_matrix, FiniteOscillator.action I g] at hh
  exact hh

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexBare.CM.FiniteOscillator

end

end OAI
