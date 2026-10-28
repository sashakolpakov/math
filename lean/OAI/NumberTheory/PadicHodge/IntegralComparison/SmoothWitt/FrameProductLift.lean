import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameDividedMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedUniversal

/-! # Frame Product Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameProductLift

noncomputable section

/-! Universal product lifts for the actual bounded smooth Witt frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (β : U ⟶ WittFrame.object p k A C ρ hρ hker hbase n)
  (σ : Type u) [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A]
  (V : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (α : V ⟶ U) (ζ : V ⟶ WittFrame.object p k A C ρ hρ hker hbase n)

local notation "W" => WittVector p k
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.object p k A C ρ hρ hker hbase n
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates.object U σ
local notation "l" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameAlgebras.chartMap p k A C ρ hρ hker hbase n U β
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameAlgebras.map p k C U V α
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameAlgebras.chartMap p k A C ρ hρ hker hbase n V ζ
local notation "hc" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameAlgebras.closed_agreement p k A C ρ hρ hker hbase n U β V ζ α

def liftAlgHom : letI := FrameLifting.ambientAlgebra p k C U
    letI := FrameLifting.ambientAlgebra p k C V
    DividedPowerAlgebra U.ring (σ →₀ U.ring) →ₐ[W] V.ring := by
  letI := FrameLifting.ambientAlgebra p k C U
  letI := FrameLifting.ambientAlgebra p k C V
  exact IntegralComparison.Etale.DividedUniversal.lift W σ A U.ring l V.ring V.ideal V.dividedPowers a b hc

def liftDP : DividedPowers.DPMorphism (G).dividedPowers V.dividedPowers := by
  letI := FrameLifting.ambientAlgebra p k C U
  letI := FrameLifting.ambientAlgebra p k C V
  exact DividedPowers.DPMorphism.mk' (IntegralComparison.Etale.DividedUniversal.lift_isDPMorphism W σ A U.ring
    U.ideal U.dividedPowers l V.ring V.ideal V.dividedPowers a α.ringMap.isDPMorphism b hc)

omit [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A] [Algebra.Etale (MvPolynomial σ (WittVector p k)) A] in
theorem lift_projection : (liftDP p k A C ρ hρ hker hbase n U β σ V α ζ).comp
    (Crystalline.DividedCoordinates.projection U σ).ringMap = α.ringMap := by
  let := FrameLifting.ambientAlgebra p k C U
  let := FrameLifting.ambientAlgebra p k C V
  apply DFunLike.ext
  intro t
  exact IntegralComparison.Etale.DividedUniversal.lift_coefficient W σ A U.ring l V.ring V.ideal V.dividedPowers a b hc t

theorem lift_frame : (liftDP p k A C ρ hρ hker hbase n U β σ V α ζ).comp
    (FrameDividedMap.relativeMap p k A C ρ hρ hker hbase n U β σ) = ζ.ringMap := by
  let := FrameLifting.ambientAlgebra p k C U
  let := FrameLifting.ambientAlgebra p k C V
  have he := IntegralComparison.Etale.DividedUniversal.lift_chart W σ A U.ring U.ideal p U.dividedPowers
    U.primeNilpotent l V.ring V.ideal V.dividedPowers a α.ringMap.isDPMorphism b hc
  apply DFunLike.ext
  intro c
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  exact AlgHom.congr_fun he c

omit [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A] [Algebra.Etale (MvPolynomial σ (WittVector p k)) A] in
theorem lift_overBase : (liftDP p k A C ρ hρ hker hbase n U β σ V α ζ).toRingHom.comp (G).base = V.base := by
  apply RingHom.ext
  intro w
  exact (DFunLike.congr_fun (lift_projection p k A C ρ hρ hker hbase n U β σ V α ζ) (U.base w)).trans
    (RingHom.congr_fun α.overBase w)

omit [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A] [Algebra.Etale (MvPolynomial σ (WittVector p k)) A] in
theorem quotient_lift_projection : (BigCrystallineSite.Object.quotientMap V G (liftDP p k A C ρ hρ hker hbase n U β σ V α ζ)).comp
    (Crystalline.DividedCoordinates.residueInclusion U σ) = BigCrystallineSite.Object.quotientMap V U α.ringMap := by
  have h := congrArg (fun φ => BigCrystallineSite.Object.quotientMap V U φ) (lift_projection p k A C ρ hρ hker hbase n U β σ V α ζ)
  exact (BigCrystallineSite.Object.quotientMap_comp V G U (liftDP p k A C ρ hρ hker hbase n U β σ V α ζ)
    (Crystalline.DividedCoordinates.projection U σ).ringMap).symm.trans h

omit [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A] [Algebra.Etale (MvPolynomial σ (WittVector p k)) A] in
theorem lift_overX : Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V G
    (liftDP p k A C ρ hρ hker hbase n U β σ V α ζ))) ≫ (G).mapToX = V.mapToX := by
  have hs : Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V G (liftDP p k A C ρ hρ hker hbase n U β σ V α ζ))) ≫
      Spec.map (CommRingCat.ofHom (Crystalline.DividedCoordinates.residueInclusion U σ)) =
        Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V U α.ringMap)) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact quotient_lift_projection p k A C ρ hρ hker hbase n U β σ V α ζ
  rw [Crystalline.DividedCoordinates.object_mapToX, ← Category.assoc, hs, α.overX]

def lift : V ⟶ G where
  ringMap := liftDP p k A C ρ hρ hker hbase n U β σ V α ζ
  overBase := lift_overBase p k A C ρ hρ hker hbase n U β σ V α ζ
  overX := lift_overX p k A C ρ hρ hker hbase n U β σ V α ζ

omit [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A] [Algebra.Etale (MvPolynomial σ (WittVector p k)) A] in
theorem lift_fst : lift p k A C ρ hρ hker hbase n U β σ V α ζ ≫ Crystalline.DividedCoordinates.projection U σ = α := by
  apply BigCrystallineSite.Object.Hom.ext
  exact lift_projection p k A C ρ hρ hker hbase n U β σ V α ζ

theorem lift_snd : lift p k A C ρ hρ hker hbase n U β σ V α ζ ≫ FrameDividedMap.frameMap p k A C ρ hρ hker hbase n U β σ = ζ := by
  apply BigCrystallineSite.Object.Hom.ext
  exact lift_frame p k A C ρ hρ hker hbase n U β σ V α ζ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameProductLift
