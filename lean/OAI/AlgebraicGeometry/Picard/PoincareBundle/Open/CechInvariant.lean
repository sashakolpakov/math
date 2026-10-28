import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.CechCoherence
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantRestriction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleLocality

/-! # Cech Invariant -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.CechInvariant

noncomputable section

/-!
# Restriction of the actual geometric Čech invariant sheaf
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z X' Y' Z' : Scheme.{u}}
  (f : X ⟶ Y) (p q : Z ⟶ X) (h : p ≫ f = q ≫ f)
  (f' : X' ⟶ Y') (p' q' : Z' ⟶ X') (h' : p' ≫ f' = q' ≫ f')
  (iY : Y' ⟶ Y) (iX : X' ⟶ X) (iZ : Z' ⟶ Z)
  [IsOpenImmersion iY] [IsOpenImmersion iX] [IsOpenImmersion iZ]
  (hf : iX ≫ f = f' ≫ iY) (hp : iZ ≫ p = p' ≫ iX) (hq : iZ ≫ q = q' ≫ iX)

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareBaseChange OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

variable (M : X.Modules)
  (σ : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback q).obj M)

/-- The original actual gluing transported by the canonical open pullback squares. -/
def gluing :
    (Scheme.Modules.pullback p').obj ((Scheme.Modules.restrictFunctor iX).obj M) ≅
      (Scheme.Modules.pullback q').obj ((Scheme.Modules.restrictFunctor iX).obj M) :=
  ((SquareBaseChange.leftSquare p p' iZ iX hp).app M ≪≫ (Scheme.Modules.restrictFunctor iZ).mapIso σ) ≪≫
    ((SquareBaseChange.leftSquare q q' iZ iX hq).app M).symm

variable (hfpre : f ⁻¹ᵁ iY.opensRange ≤ iX.opensRange)
  (hqpre : q ⁻¹ᵁ iX.opensRange ≤ iZ.opensRange)

/-- The actual global geometric invariant restricts to the actual invariant on an open square. -/
def invariantIso :
    (Scheme.Modules.restrictFunctor iY).obj (Geometric.CechInvariant.invariantSheaf f p q h M σ) ≅
      Geometric.CechInvariant.invariantSheaf f' p' q' h' ((Scheme.Modules.restrictFunctor iX).obj M)
        (gluing p q p' q' iX iZ hp hq M σ) := by
  have := ModuleLocality.restrict_preservesFiniteLimits iY
  have := SquareBaseChange.rightMate_isIso f f' iX iY hf hfpre
  have := SquareBaseChange.rightMate_isIso q q' iZ iX hq hqpre
  exact Cech.InvariantRestriction.invariantIso
    (Scheme.Modules.pullbackPushforwardAdjunction f) (Scheme.Modules.pullbackPushforwardAdjunction f')
    (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction p')
    (Scheme.Modules.pullbackPushforwardAdjunction q) (Scheme.Modules.pullbackPushforwardAdjunction q')
    (SquareBaseChange.leftSquare f f' iX iY hf) (SquareBaseChange.leftSquare p p' iZ iX hp) (SquareBaseChange.leftSquare q q' iZ iX hq)
    (Geometric.CechInvariant.directImageIso f p q h) (Geometric.CechInvariant.directImageIso f' p' q' h') σ.hom
    (CechCoherence.right_coherent f p q h f' p' q' h' iY iX iZ hf hp hq)

/-- Restriction preserves the actual canonical comparison, including its open pullback square. -/
theorem comparison_fac :
    (Scheme.Modules.pullback f').map (invariantIso f p q h f' p' q' h' iY iX iZ hf hp hq M σ
      hfpre hqpre).hom ≫
      Geometric.CechInvariant.comparison f' p' q' h' ((Scheme.Modules.restrictFunctor iX).obj M)
        (gluing p q p' q' iX iZ hp hq M σ) =
    (SquareBaseChange.leftSquare f f' iX iY hf).hom.app (Geometric.CechInvariant.invariantSheaf f p q h M σ) ≫
      (Scheme.Modules.restrictFunctor iX).map (Geometric.CechInvariant.comparison f p q h M σ) := by
  have := ModuleLocality.restrict_preservesFiniteLimits iY
  have := SquareBaseChange.rightMate_isIso f f' iX iY hf hfpre
  have := SquareBaseChange.rightMate_isIso q q' iZ iX hq hqpre
  exact Cech.InvariantRestriction.comparison_fac
    (Scheme.Modules.pullbackPushforwardAdjunction f) (Scheme.Modules.pullbackPushforwardAdjunction f')
    (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction p')
    (Scheme.Modules.pullbackPushforwardAdjunction q) (Scheme.Modules.pullbackPushforwardAdjunction q')
    (SquareBaseChange.leftSquare f f' iX iY hf) (SquareBaseChange.leftSquare p p' iZ iX hp) (SquareBaseChange.leftSquare q q' iZ iX hq)
    (Geometric.CechInvariant.directImageIso f p q h) (Geometric.CechInvariant.directImageIso f' p' q' h') σ.hom
    (CechCoherence.right_coherent f p q h f' p' q' h' iY iX iZ hf hp hq)

include hf hfpre hqpre in
/-- Effectivity on the restricted geometric diagram detects the restricted global comparison. -/
theorem comparison_map_isIso_iff :
    IsIso ((Scheme.Modules.restrictFunctor iX).map (Geometric.CechInvariant.comparison f p q h M σ)) ↔
      IsIso (Geometric.CechInvariant.comparison f' p' q' h' ((Scheme.Modules.restrictFunctor iX).obj M)
        (gluing p q p' q' iX iZ hp hq M σ)) := by
  have := ModuleLocality.restrict_preservesFiniteLimits iY
  have := SquareBaseChange.rightMate_isIso f f' iX iY hf hfpre
  have := SquareBaseChange.rightMate_isIso q q' iZ iX hq hqpre
  exact Cech.InvariantRestriction.comparison_map_isIso_iff
    (Scheme.Modules.pullbackPushforwardAdjunction f) (Scheme.Modules.pullbackPushforwardAdjunction f')
    (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction p')
    (Scheme.Modules.pullbackPushforwardAdjunction q) (Scheme.Modules.pullbackPushforwardAdjunction q')
    (SquareBaseChange.leftSquare f f' iX iY hf) (SquareBaseChange.leftSquare p p' iZ iX hp) (SquareBaseChange.leftSquare q q' iZ iX hq)
    (Geometric.CechInvariant.directImageIso f p q h) (Geometric.CechInvariant.directImageIso f' p' q' h') σ.hom
    (CechCoherence.right_coherent f p q h f' p' q' h' iY iX iZ hf hp hq)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.CechInvariant
