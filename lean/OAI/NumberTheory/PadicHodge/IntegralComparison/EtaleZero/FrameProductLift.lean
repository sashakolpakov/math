import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedUniversal

/-! # Frame Product Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameProductLift

noncomputable section

/-!
# IntegralComparison: product lifts for original étale zero frames
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [CharP k p]
  [CommRing C] [Algebra k C] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (β : U ⟶ ZeroLevel.LevelFrame.frame p k C)
  (V : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (α : V ⟶ U) (ζ : V ⟶ ZeroLevel.LevelFrame.frame p k C)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.frame p k C
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates.object U σ
local notation "l" => OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameAlgebras.chartMap p k C U β
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameAlgebras.map p k C U β V ζ α
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameAlgebras.chartMap p k C V ζ
local notation "hc" => OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameAlgebras.closed_agreement p k C U β V ζ α

def liftAlgHom : letI := Zero.FrameAlgebras.ambientAlgebra p k C U β
    letI := Zero.FrameAlgebras.ambientAlgebra p k C V ζ
    DividedPowerAlgebra U.ring (σ →₀ U.ring) →ₐ[k] V.ring := by
  letI := Zero.FrameAlgebras.ambientAlgebra p k C U β
  letI := Zero.FrameAlgebras.ambientAlgebra p k C V ζ
  exact IntegralComparison.Etale.DividedUniversal.lift k σ C U.ring l V.ring V.ideal V.dividedPowers a b hc

def liftDP : DividedPowers.DPMorphism (G).dividedPowers V.dividedPowers := by
  letI := Zero.FrameAlgebras.ambientAlgebra p k C U β
  letI := Zero.FrameAlgebras.ambientAlgebra p k C V ζ
  exact DividedPowers.DPMorphism.mk' (IntegralComparison.Etale.DividedUniversal.lift_isDPMorphism k σ C U.ring
    U.ideal U.dividedPowers l V.ring V.ideal V.dividedPowers a α.ringMap.isDPMorphism b hc)

omit [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C] in
theorem lift_projection : (liftDP p k C σ U β V α ζ).comp
    (Crystalline.DividedCoordinates.projection U σ).ringMap = α.ringMap := by
  let := Zero.FrameAlgebras.ambientAlgebra p k C U β
  let := Zero.FrameAlgebras.ambientAlgebra p k C V ζ
  apply DFunLike.ext
  intro t
  exact IntegralComparison.Etale.DividedUniversal.lift_coefficient k σ C U.ring l V.ring V.ideal V.dividedPowers a b hc t

theorem lift_frame : (liftDP p k C σ U β V α ζ).comp
    (FrameMap.relativeMap p k C σ U β) = ζ.ringMap := by
  let := Zero.FrameAlgebras.ambientAlgebra p k C U β
  let := Zero.FrameAlgebras.ambientAlgebra p k C V ζ
  have he := IntegralComparison.Etale.DividedUniversal.lift_chart k σ C U.ring U.ideal p U.dividedPowers
    U.primeNilpotent l V.ring V.ideal V.dividedPowers a α.ringMap.isDPMorphism b hc
  apply DFunLike.ext
  intro c
  exact AlgHom.congr_fun he c

omit [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C] in
theorem lift_overBase : (liftDP p k C σ U β V α ζ).toRingHom.comp (G).base = V.base := by
  apply RingHom.ext
  intro w
  exact (DFunLike.congr_fun (lift_projection p k C σ U β V α ζ) (U.base w)).trans
    (RingHom.congr_fun α.overBase w)

omit [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C] in
theorem quotient_lift_projection : (BigCrystallineSite.Object.quotientMap V G (liftDP p k C σ U β V α ζ)).comp
    (Crystalline.DividedCoordinates.residueInclusion U σ) = BigCrystallineSite.Object.quotientMap V U α.ringMap := by
  have h := congrArg (fun φ => BigCrystallineSite.Object.quotientMap V U φ) (lift_projection p k C σ U β V α ζ)
  exact (BigCrystallineSite.Object.quotientMap_comp V G U (liftDP p k C σ U β V α ζ)
    (Crystalline.DividedCoordinates.projection U σ).ringMap).symm.trans h

omit [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C] in
theorem lift_overX : Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V G
    (liftDP p k C σ U β V α ζ))) ≫ (G).mapToX = V.mapToX := by
  have hs : Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V G (liftDP p k C σ U β V α ζ))) ≫
      Spec.map (CommRingCat.ofHom (Crystalline.DividedCoordinates.residueInclusion U σ)) =
        Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V U α.ringMap)) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact quotient_lift_projection p k C σ U β V α ζ
  rw [Crystalline.DividedCoordinates.object_mapToX, ← Category.assoc, hs, α.overX]

def lift : V ⟶ G where
  ringMap := liftDP p k C σ U β V α ζ
  overBase := lift_overBase p k C σ U β V α ζ
  overX := lift_overX p k C σ U β V α ζ

omit [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C] in
theorem lift_fst : lift p k C σ U β V α ζ ≫ Crystalline.DividedCoordinates.projection U σ = α := by
  apply BigCrystallineSite.Object.Hom.ext
  exact lift_projection p k C σ U β V α ζ

theorem lift_snd : lift p k C σ U β V α ζ ≫ FrameMap.frameMap p k C σ U β = ζ := by
  apply BigCrystallineSite.Object.Hom.ext
  exact lift_frame p k C σ U β V α ζ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameProductLift
