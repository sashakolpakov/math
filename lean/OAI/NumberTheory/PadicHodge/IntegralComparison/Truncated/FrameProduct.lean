import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameDividedMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedUniversal

/-! # Frame Product -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameProduct.Lift

/-! Universal product lifts for actual smooth finite-Witt-level frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

attribute [local instance] IntegralComparison.Etale.DividedCoordinateLift.scalarAlgebra
  IntegralComparison.Etale.DividedCoordinateLift.scalarTower

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C : Type) [CommRing A] [CommRing C]
  [Algebra (Witt.Ring p k n) A]
  [Algebra.Smooth (Witt.Ring p k n) A] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Witt.Ring p k n) A (Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (β : U ⟶ SmoothFrame.object p A C ρ hρ hker k n hbase)
  (σ : Type) [Algebra (MvPolynomial σ (Witt.Ring p k n)) A]
  [IsScalarTower (Witt.Ring p k n)
    (MvPolynomial σ (Witt.Ring p k n)) A]
  [Algebra.Etale (MvPolynomial σ (Witt.Ring p k n)) A]
  (V : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (α : V ⟶ U) (ζ : V ⟶ SmoothFrame.object p A C ρ hρ hker k n hbase)

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.object p A C ρ hρ hker k n hbase
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates.object U σ
local notation "l" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras.chartMap p k n A C ρ hρ hker hbase U β
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras.map p k n A C ρ hρ hker hbase U β V ζ α
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras.chartMap p k n A C ρ hρ hker hbase V ζ
local notation "hc" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras.closed_agreement p k n A C ρ hρ hker hbase U β V ζ α

def liftAlgHom : letI := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U β
    letI := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase V ζ
    DividedPowerAlgebra U.ring (σ →₀ U.ring) →ₐ[S] V.ring := by
  letI := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U β
  letI := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase V ζ
  exact IntegralComparison.Etale.DividedUniversal.lift S σ A U.ring l V.ring V.ideal V.dividedPowers a b hc

def liftDP : DividedPowers.DPMorphism (G).dividedPowers V.dividedPowers := by
  letI := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U β
  letI := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase V ζ
  exact DividedPowers.DPMorphism.mk' (IntegralComparison.Etale.DividedUniversal.lift_isDPMorphism S σ A U.ring
    U.ideal U.dividedPowers l V.ring V.ideal V.dividedPowers a α.ringMap.isDPMorphism b hc)

omit [Fintype k] [IsScalarTower S (MvPolynomial σ S) A] [Algebra.Etale (MvPolynomial σ S) A] in
theorem lift_projection : (liftDP p k n A C ρ hρ hker hbase U β σ V α ζ).comp
    (Crystalline.DividedCoordinates.projection U σ).ringMap = α.ringMap := by
  let := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U β
  let := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase V ζ
  apply DFunLike.ext
  intro t
  exact IntegralComparison.Etale.DividedUniversal.lift_coefficient S σ A U.ring l V.ring V.ideal V.dividedPowers a b hc t

omit [Fintype k] in
theorem lift_frame : (liftDP p k n A C ρ hρ hker hbase U β σ V α ζ).comp
    (FrameDividedMap.relativeMap p k n A C ρ hρ hker hbase U β σ) = ζ.ringMap := by
  let := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U β
  let := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase V ζ
  have he := IntegralComparison.Etale.DividedUniversal.lift_chart S σ A U.ring U.ideal p U.dividedPowers
    U.primeNilpotent l V.ring V.ideal V.dividedPowers a α.ringMap.isDPMorphism b hc
  apply DFunLike.ext
  intro c
  exact AlgHom.congr_fun he c

omit [Fintype k] [IsScalarTower S (MvPolynomial σ S) A] [Algebra.Etale (MvPolynomial σ S) A] in
theorem lift_overBase : (liftDP p k n A C ρ hρ hker hbase U β σ V α ζ).toRingHom.comp (G).base = V.base := by
  apply RingHom.ext
  intro w
  exact (DFunLike.congr_fun (lift_projection p k n A C ρ hρ hker hbase U β σ V α ζ) (U.base w)).trans
    (RingHom.congr_fun α.overBase w)

omit [Fintype k] [IsScalarTower S (MvPolynomial σ S) A] [Algebra.Etale (MvPolynomial σ S) A] in
theorem quotient_lift_projection : (BigCrystallineSite.Object.quotientMap V G (liftDP p k n A C ρ hρ hker hbase U β σ V α ζ)).comp
    (Crystalline.DividedCoordinates.residueInclusion U σ) = BigCrystallineSite.Object.quotientMap V U α.ringMap := by
  have h := congrArg (fun φ => BigCrystallineSite.Object.quotientMap V U φ) (lift_projection p k n A C ρ hρ hker hbase U β σ V α ζ)
  exact (BigCrystallineSite.Object.quotientMap_comp V G U (liftDP p k n A C ρ hρ hker hbase U β σ V α ζ)
    (Crystalline.DividedCoordinates.projection U σ).ringMap).symm.trans h

omit [Fintype k] [IsScalarTower S (MvPolynomial σ S) A] [Algebra.Etale (MvPolynomial σ S) A] in
theorem lift_overX : Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V G
    (liftDP p k n A C ρ hρ hker hbase U β σ V α ζ))) ≫ (G).mapToX = V.mapToX := by
  have hs : Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V G (liftDP p k n A C ρ hρ hker hbase U β σ V α ζ))) ≫
      Spec.map (CommRingCat.ofHom (Crystalline.DividedCoordinates.residueInclusion U σ)) =
        Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V U α.ringMap)) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact quotient_lift_projection p k n A C ρ hρ hker hbase U β σ V α ζ
  rw [Crystalline.DividedCoordinates.object_mapToX, ← Category.assoc, hs, α.overX]

def lift : V ⟶ G where
  ringMap := liftDP p k n A C ρ hρ hker hbase U β σ V α ζ
  overBase := lift_overBase p k n A C ρ hρ hker hbase U β σ V α ζ
  overX := lift_overX p k n A C ρ hρ hker hbase U β σ V α ζ

omit [Fintype k] [IsScalarTower S (MvPolynomial σ S) A] [Algebra.Etale (MvPolynomial σ S) A] in
theorem lift_fst : lift p k n A C ρ hρ hker hbase U β σ V α ζ ≫ Crystalline.DividedCoordinates.projection U σ = α := by
  apply BigCrystallineSite.Object.Hom.ext
  exact lift_projection p k n A C ρ hρ hker hbase U β σ V α ζ

omit [Fintype k] in
theorem lift_snd : lift p k n A C ρ hρ hker hbase U β σ V α ζ ≫ FrameDividedMap.frameMap p k n A C ρ hρ hker hbase U β σ = ζ := by
  apply BigCrystallineSite.Object.Hom.ext
  exact lift_frame p k n A C ρ hρ hker hbase U β σ V α ζ

end NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameProduct.Lift

namespace NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameProduct

/-! Products of actual smooth finite-level frames are free divided-coordinate extensions. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

attribute [local instance] IntegralComparison.Etale.DividedCoordinateLift.scalarAlgebra
  IntegralComparison.Etale.DividedCoordinateLift.scalarTower

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C : Type) [CommRing A] [CommRing C]
  [Algebra (Witt.Ring p k n) A]
  [Algebra.Smooth (Witt.Ring p k n) A] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Witt.Ring p k n) A (Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (β : U ⟶ SmoothFrame.object p A C ρ hρ hker k n hbase)
  (σ : Type) [Algebra (MvPolynomial σ (Witt.Ring p k n)) A]
  [IsScalarTower (Witt.Ring p k n)
    (MvPolynomial σ (Witt.Ring p k n)) A]
  [Algebra.Etale (MvPolynomial σ (Witt.Ring p k n)) A]
  (V : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (α : V ⟶ U) (ζ : V ⟶ SmoothFrame.object p A C ρ hρ hker k n hbase)

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.object p A C ρ hρ hker k n hbase
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates.object U σ
local notation "l" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras.chartMap p k n A C ρ hρ hker hbase U β
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras.map p k n A C ρ hρ hker hbase U β V ζ α
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras.chartMap p k n A C ρ hρ hker hbase V ζ
local notation "hc" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras.closed_agreement p k n A C ρ hρ hker hbase U β V ζ α

def asAlgHom (g : V ⟶ G) (hfst : g ≫ Crystalline.DividedCoordinates.projection U σ = α) :
    letI := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U β
    letI := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase V ζ
    DividedPowerAlgebra U.ring (σ →₀ U.ring) →ₐ[S] V.ring := by
  letI := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U β
  letI := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase V ζ
  refine { g.ringMap.toRingHom with commutes' := ?_ }
  intro r
  have he := congrArg (fun m : V ⟶ U => m.ringMap (algebraMap S U.ring r)) hfst
  exact he.trans ((a).commutes r)

omit [Fintype k] in
theorem lift_unique (g : V ⟶ G)
    (hfst : g ≫ Crystalline.DividedCoordinates.projection U σ = α)
    (hsnd : g ≫ FrameDividedMap.frameMap p k n A C ρ hρ hker hbase U β σ = ζ) :
    g = Lift.lift p k n A C ρ hρ hker hbase U β σ V α ζ := by
  let := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U β
  let := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase V ζ
  let gA := asAlgHom p k n A C ρ hρ hker hbase U β σ V α ζ g hfst
  have hcoeff (t : U.ring) : gA (algebraMap U.ring (G).ring t) = a t :=
    congrArg (fun m : V ⟶ U => m.ringMap t) hfst
  have hchart : gA.comp (FrameDividedMap.chartLift p k n A C ρ hρ hker hbase U β σ) = b := by
    apply AlgHom.ext
    intro c
    exact congrArg (fun m : V ⟶ F => m.ringMap c) hsnd
  have he := IntegralComparison.Etale.DividedUniversal.lift_unique S σ A U.ring U.ideal p U.dividedPowers
    U.primeNilpotent l V.ring V.ideal V.dividedPowers a b hc gA g.ringMap.isDPMorphism hcoeff hchart
  apply BigCrystallineSite.Object.Hom.ext
  apply DFunLike.ext
  intro z
  exact AlgHom.congr_fun he z

/-- The actual smooth finite-level frame product in the original crystalline category. -/
def isProduct : IsLimit (FrameDividedMap.cone p k n A C ρ hρ hker hbase U β σ) :=
  BinaryFan.isLimitMk
    (fun c => Lift.lift p k n A C ρ hρ hker hbase U β σ c.pt c.fst c.snd)
    (fun c => Lift.lift_fst p k n A C ρ hρ hker hbase U β σ c.pt c.fst c.snd)
    (fun c => Lift.lift_snd p k n A C ρ hρ hker hbase U β σ c.pt c.fst c.snd)
    (fun c m hfst hsnd => lift_unique p k n A C ρ hρ hker hbase U β σ c.pt c.fst c.snd m hfst hsnd)

end NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameProduct

end

end OAI
