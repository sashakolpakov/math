import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameProductLift

/-! # Frame Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameProduct

noncomputable section

/-! The actual smooth Witt frame products are native free divided-coordinate extensions. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

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

def asAlgHom (g : V ⟶ G) (hfst : g ≫ Crystalline.DividedCoordinates.projection U σ = α) :
    letI := FrameLifting.ambientAlgebra p k C U
    letI := FrameLifting.ambientAlgebra p k C V
    DividedPowerAlgebra U.ring (σ →₀ U.ring) →ₐ[W] V.ring := by
  letI := FrameLifting.ambientAlgebra p k C U
  letI := FrameLifting.ambientAlgebra p k C V
  refine { g.ringMap.toRingHom with commutes' := ?_ }
  intro r
  have he := congrArg (fun m : V ⟶ U => m.ringMap (algebraMap W U.ring r)) hfst
  exact he.trans ((a).commutes r)

theorem lift_unique (g : V ⟶ G)
    (hfst : g ≫ Crystalline.DividedCoordinates.projection U σ = α)
    (hsnd : g ≫ FrameDividedMap.frameMap p k A C ρ hρ hker hbase n U β σ = ζ) :
    g = FrameProductLift.lift p k A C ρ hρ hker hbase n U β σ V α ζ := by
  let := FrameLifting.ambientAlgebra p k C U
  let := FrameLifting.ambientAlgebra p k C V
  let gA := asAlgHom p k C U σ V α g hfst
  have hcoeff (t : U.ring) : gA (algebraMap U.ring (G).ring t) = a t :=
    congrArg (fun m : V ⟶ U => m.ringMap t) hfst
  have hchart : gA.comp (FrameDividedMap.chartLift p k A C ρ hρ hker hbase n U β σ) = b := by
    apply AlgHom.ext
    intro c
    exact congrArg (fun m : V ⟶ F => m.ringMap (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1)) c)) hsnd
  have he := IntegralComparison.Etale.DividedUniversal.lift_unique W σ A U.ring U.ideal p U.dividedPowers
    U.primeNilpotent l V.ring V.ideal V.dividedPowers a b hc gA g.ringMap.isDPMorphism hcoeff hchart
  apply BigCrystallineSite.Object.Hom.ext
  apply DFunLike.ext
  intro z
  exact AlgHom.congr_fun he z

/-- The actual smooth Witt frame product in the original crystalline category. -/
def isProduct : IsLimit (FrameDividedMap.cone p k A C ρ hρ hker hbase n U β σ) :=
  BinaryFan.isLimitMk
    (fun c => FrameProductLift.lift p k A C ρ hρ hker hbase n U β σ c.pt c.fst c.snd)
    (fun c => FrameProductLift.lift_fst p k A C ρ hρ hker hbase n U β σ c.pt c.fst c.snd)
    (fun c => FrameProductLift.lift_snd p k A C ρ hρ hker hbase n U β σ c.pt c.fst c.snd)
    (fun c m hfst hsnd => lift_unique p k A C ρ hρ hker hbase n U β σ c.pt c.fst c.snd m hfst hsnd)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameProduct
