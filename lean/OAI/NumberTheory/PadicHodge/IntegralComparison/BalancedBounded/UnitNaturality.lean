import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CupUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CupRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.GeometricCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ExteriorNaturality

/-! # Unit Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.UnitNaturality

noncomputable section

/-! The balanced native coefficient-one class is independent of covering
refinement and natural for the actual bounded crystalline pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι κ : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (G : κ → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) (ρ : ι → κ)
  (α : ∀ i, F i ⟶ G (ρ i))
  (hF : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ BoundedCrystalline.Site.topology f n U)
  (hG : ∀ U, CoveringObjectsSheafDetection.sieve G U ∈ BoundedCrystalline.Site.topology f n U)

include ρ α in
theorem refinement : CupUnit.one p k f n F hF =
    CupUnit.one p k f n G hG :=
  (congrArg (CechCup.cohomologyEquiv p k f n F hF 0)
    (Cosimplicial.ExteriorNaturality.Cup.cohomologyOne_natural
      (Bounded.CupFamilyRefinement.Family.map p k f n F G ρ α))).symm.trans
    (CupRefinement.equivalence_natural p k f n F G ρ α hF hG 0
      (Cosimplicial.ModuleCupAlgebra.cohomologyOne (BoundedCrystalline.CechCup.cochainAlgebra f n G)))

end

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of (WittVector p k))}
  {fY : Y ⟶ Spec (CommRingCat.of (WittVector p k))}
  [IsSeparated f] [IsSeparated fY]
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  {ι κ : Type u} (FX : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (FY : κ → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n) (ρ : ι → κ)
  (α : ∀ i, (BoundedOpen.Equivalence.postcompose g hg n).obj (FX i) ⟶ FY (ρ i))
  (hX : ∀ V, CoveringObjectsSheafDetection.sieve FX V ∈ BoundedCrystalline.Site.topology f n V)
  (hY : ∀ V, CoveringObjectsSheafDetection.sieve FY V ∈ BoundedCrystalline.Site.topology fY n V)

include ρ α in
theorem pullback : BoundedCrystalline.CrystallinePullback.pullback g hg n 0
      (CupUnit.one p k fY n FY hY) =
    CupUnit.one p k f n FX hX :=
  (GeometricCup.equivalence_natural p k g hg n FX FY ρ α hX hY 0
    (Cosimplicial.ModuleCupAlgebra.cohomologyOne (BoundedCrystalline.CechCup.cochainAlgebra fY n FY))).symm.trans
    (congrArg (CechCup.cohomologyEquiv p k f n FX hX 0)
      (Cosimplicial.ExteriorNaturality.Cup.cohomologyOne_natural
        (BoundedCrystalline.CupRefinement.map g hg n FX FY ρ α)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.UnitNaturality
