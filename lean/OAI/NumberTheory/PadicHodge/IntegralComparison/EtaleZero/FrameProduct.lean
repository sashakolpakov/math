import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameProductLift

/-! # Frame Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameProduct

noncomputable section

/-!
# IntegralComparison: products with original étale zero frames are free divided-coordinate extensions
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

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

def asAlgHom (g : V ⟶ G) (hfst : g ≫ Crystalline.DividedCoordinates.projection U σ = α) :
    letI := Zero.FrameAlgebras.ambientAlgebra p k C U β
    letI := Zero.FrameAlgebras.ambientAlgebra p k C V ζ
    DividedPowerAlgebra U.ring (σ →₀ U.ring) →ₐ[k] V.ring := by
  letI := Zero.FrameAlgebras.ambientAlgebra p k C U β
  letI := Zero.FrameAlgebras.ambientAlgebra p k C V ζ
  refine { g.ringMap.toRingHom with commutes' := ?_ }
  intro r
  have he := congrArg (fun m : V ⟶ U => m.ringMap (algebraMap k U.ring r)) hfst
  exact he.trans ((a).commutes r)

theorem lift_unique (g : V ⟶ G)
    (hfst : g ≫ Crystalline.DividedCoordinates.projection U σ = α)
    (hsnd : g ≫ FrameMap.frameMap p k C σ U β = ζ) :
    g = FrameProductLift.lift p k C σ U β V α ζ := by
  let := Zero.FrameAlgebras.ambientAlgebra p k C U β
  let := Zero.FrameAlgebras.ambientAlgebra p k C V ζ
  let gA := asAlgHom p k C σ U β V α ζ g hfst
  have hbase (t : U.ring) : gA (algebraMap U.ring (G).ring t) = a t :=
    congrArg (fun m : V ⟶ U => m.ringMap t) hfst
  have hchart : gA.comp (FrameMap.chartLift p k C σ U β) = b := by
    apply AlgHom.ext
    intro c
    exact congrArg (fun m : V ⟶ F => m.ringMap c) hsnd
  have he := IntegralComparison.Etale.DividedUniversal.lift_unique k σ C U.ring U.ideal p U.dividedPowers
    U.primeNilpotent l V.ring V.ideal V.dividedPowers a b hc gA g.ringMap.isDPMorphism hbase hchart
  apply BigCrystallineSite.Object.Hom.ext
  apply DFunLike.ext
  intro z
  exact AlgHom.congr_fun he z

/-- The actual zero-frame product in the original crystalline category. -/
def isProduct : IsLimit (FrameMap.cone p k C σ U β) :=
  BinaryFan.isLimitMk
    (fun c => FrameProductLift.lift p k C σ U β c.pt c.fst c.snd)
    (fun c => FrameProductLift.lift_fst p k C σ U β c.pt c.fst c.snd)
    (fun c => FrameProductLift.lift_snd p k C σ U β c.pt c.fst c.snd)
    (fun c m hfst hsnd => lift_unique p k C σ U β c.pt c.fst c.snd m hfst hsnd)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameProduct
