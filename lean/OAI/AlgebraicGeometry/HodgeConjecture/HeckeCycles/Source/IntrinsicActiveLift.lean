import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalOscillator
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicActiveClosure
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OscillatorClosure
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialLinearOscillatorLift
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.Sl

/-! # Intrinsic Active Lift -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicActiveLift.CM.IntrinsicOscillator

/-! A smooth extension of the actual rational source action is unitary
and has the actual source Heisenberg projection on the supported active subgroup. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  (ρ : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates) →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)))
  (hρ : ∀ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places), IsOpen {g | ρ g φ = φ})
  (hr : ρ.comp (SourceAdelic.ThetaRationalTheta.CM.rational E L) = WeilData.CM.finiteAction E L)

include hρ hr in
theorem on_closure
    (g : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (hg : g ∈ (RationalLocal.CM.finiteHom E
      (OppositeCoordinates.CM.coordinates E L.coordinates)).range.topologicalClosure) :
    (∀ φ ψ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places),
      Finite.FiniteOscillator.CM.integralPairing (ρ g φ) (ρ g ψ) = Finite.FiniteOscillator.CM.integralPairing φ ψ) ∧
    (∀ (v : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)),
      ρ g (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) φ) =
        Finite.FourierHeisenberg.CM.operator
          (fun i => ((ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates g).val *ᵥ v) (.inl i))
          (fun i => ((ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates g).val *ᵥ v) (.inr i)) (ρ g φ)) :=
  OscillatorClosure.CM.Rational.apply ρ hρ
    (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates)
    (SourceFinite.ProjectionTopology.CM.original_action E L.coordinates)
    (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (RationalOscillator.CM.unitary E L ρ hr)
    (RationalOscillator.CM.covariance E L ρ hr) g hg

variable {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

include hρ hr in
theorem active_unitary (u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q])
    (φ ψ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    Finite.FiniteOscillator.CM.integralPairing
      (ρ (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, 1)) φ)
      (ρ (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, 1)) ψ) =
        Finite.FiniteOscillator.CM.integralPairing φ ψ :=
  (on_closure E L ρ hρ hr _ (IntrinsicActiveClosure.CM.Intrinsic.image_mem_closure E L f (u, 1))).1 φ ψ

include hρ hr in
theorem active_covariance (u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q])
    (v : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    ρ (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, 1))
      (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) φ) =
        Finite.FourierHeisenberg.CM.operator
          (fun i => ((ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
            (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, 1))).val *ᵥ v) (.inl i))
          (fun i => ((ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
            (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, 1))).val *ᵥ v) (.inr i))
          (ρ (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, 1)) φ) :=
  (on_closure E L ρ hρ hr _ (IntrinsicActiveClosure.CM.Intrinsic.image_mem_closure E L f (u, 1))).2 v φ

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicActiveLift.CM.IntrinsicOscillator

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicActiveLift

/-! The supported active part of any smooth extension of the actual
source action has the same genuine metaplectic lift as the original source. -/

attribute [local instance 2000] Subgroup.toGroup Prod.instGroup
open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

namespace CM.Intrinsic

private def restrictLeft {A B G : Type*} [Group A] [Group B] [Group G]
    (f : A × B →* G) : A →* G :=
  f.comp (MonoidHom.inl A B)

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  (ρ : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates) →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)))
  (hρ : ∀ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places), IsOpen {g | ρ g φ = φ})
  (hr : ρ.comp (SourceAdelic.ThetaRationalTheta.CM.rational E L) = WeilData.CM.finiteAction E L)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

local instance activeLiftAwayGroup : Group (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  Subgroup.toGroup (FactorTheta.CM.RationalWeilFactorization.Away E L f)

local instance activeLiftAwayMulOneClass :
    MulOneClass (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  SubmonoidClass.toMulOneClass (FactorTheta.CM.RationalWeilFactorization.Away E L f)

local instance activeLiftSourceMulOneClass :
    MulOneClass (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] ×
      FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  (show Group (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] ×
    FactorTheta.CM.RationalWeilFactorization.Away E L f) from Prod.instGroup).toMulOneClass

def inclusion := restrictLeft (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f)

def oscillator : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] →*
    Finite.FiniteOscillator.CM.Oscillator (I := GeometricSource.CM.Positions E places) :=
  OscillatorHomAssembly.CM.lift
    ((ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates).comp (inclusion E L f))
    (ρ.comp (inclusion E L f)) (IntrinsicOscillator.active_unitary E L ρ hρ hr f)
    (IntrinsicOscillator.active_covariance E L ρ hρ hr f)

def lift : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] →* WeilData.CM.FiniteCoverGroup E places :=
  (WeilReindexBare.CM.lift (GeometricSource.CM.Positions E places)).comp
    (SpecialLinearOscillatorLift.CM.lift (oscillator E L ρ hρ hr f))

theorem projection_matrix (u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    ((WeilData.CM.weilData E places).finite.project (lift E L ρ hρ hr f u)).val =
      (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
        (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, 1))).val :=
  (WeilReindexBare.CM.projection_matrix (GeometricSource.CM.Positions E places)
    (SpecialLinearOscillatorLift.CM.lift (oscillator E L ρ hρ hr f) u)).trans
      (OscillatorHomAssembly.CM.projection_matrix
        ((ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates).comp (inclusion E L f))
        (ρ.comp (inclusion E L f)) (IntrinsicOscillator.active_unitary E L ρ hρ hr f)
        (IntrinsicOscillator.active_covariance E L ρ hρ hr f) u)

theorem action (u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    (WeilData.CM.weilData E places).finite.action (lift E L ρ hρ hr f u) φ =
      ρ (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, 1)) φ :=
  WeilReindexBare.CM.action (GeometricSource.CM.Positions E places)
    (SpecialLinearOscillatorLift.CM.lift (oscillator E L ρ hρ hr f) u) φ

theorem lift_eq : lift E L ρ hρ hr f = ReferenceActiveWeil.CM.Reference.lift E L.coordinates f := by
  apply CMExtraction.Finite.Sl.Local.finite_sl3_lift_unique q (WeilData.CM.weilData E places)
  intro u
  apply Subtype.ext
  exact (projection_matrix E L ρ hρ hr f u).trans
    ((congrArg (fun g : SourceFinite.Product.CM.FiniteGroup E
      (OppositeCoordinates.CM.coordinates E L.coordinates) =>
        (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates g).val)
        (IntrinsicActiveClosure.CM.Intrinsic.active E L f u)).trans
      (congrArg Subtype.val (ReferenceActiveWeil.CM.ReferenceFiniteProjection.active E L.coordinates f u)).symm)

include hρ hr in
theorem source_action (u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    ρ (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, 1)) φ =
      (WeilData.CM.weilData E places).finite.action
        (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f u) φ :=
  (Intrinsic.action E L ρ hρ hr f u φ).symm.trans
    (congrArg (fun a : WeilData.CM.FiniteCoverGroup E places =>
      (WeilData.CM.weilData E places).finite.action a φ)
      (DFunLike.congr_fun (lift_eq E L ρ hρ hr f) u))

end CM.Intrinsic

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicActiveLift

end

end OAI
