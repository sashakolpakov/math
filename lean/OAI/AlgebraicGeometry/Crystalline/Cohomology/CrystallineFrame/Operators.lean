import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Constants

/-! # Operators -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators

noncomputable section

/-!
# Natural differentials on crystalline frame functions

Coordinate differentiation commutes with the affine transition maps of
the actual frame extension. Coefficient inclusion is natural. Coordinate
primitives and evaluation at the chosen origin are defined objectwise;
their naturality is not required for the augmented resolution.
-/

open _root_.CategoryTheory Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X

def functions : Cᵒᵖ ⥤ ModuleCat W :=
  (Functor.CrystallineFrameFunctor.functor p k B σ a).op ⋙ Site.functions p k X

def derivative (i : σ) : functions p k B σ a ⟶ functions p k B σ a where
  app Q := ModuleCat.ofHom
    ((FreeDivided.Derivation.FreeDividedDerivation.derivation Q.unop.thickening.ring σ i).toLinearMap.restrictScalars W)
  naturality {Q P} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    let : Algebra Q.unop.thickening.ring P.unop.thickening.ring := f.unop.ambientMap.toRingHom.toAlgebra
    exact Divided.AffineMaps.DividedAffineMaps.derivation_naturality Q.unop.thickening.ring P.unop.thickening.ring σ
      (RingHom.ker P.unop.thickening.reduction) P.unop.thickening.dividedPowers
      (Lifts.CrystallineFrameLifts.translation a f.unop) (Lifts.CrystallineFrameLifts.translation_mem a f.unop) i t

def coefficients : Site.functions p k X ⟶ functions p k B σ a where
  app Q := ModuleCat.ofHom
    ((PolynomialThickening.CrystallinePolynomialThickening.inclusion p k Q.unop.residueRing σ Q.unop.thickening).hom.toLinearMap)
  naturality {Q P} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact (Map.CrystallineFrameMap.ambientMap_coefficient a f.unop t).symm

def primitive (Q : Cᵒᵖ) (i : σ) : Module.End W ((functions p k B σ a).obj Q) :=
  (FreeDivided.Primitive.FreeDividedPrimitive.primitive Q.unop.thickening.ring σ i).restrictScalars W

def retraction (Q : Cᵒᵖ) : (functions p k B σ a).obj Q →ₗ[W] (Site.functions p k X).obj Q :=
  (PolynomialThickening.CrystallinePolynomialThickening.augmentation p k Q.unop.residueRing σ Q.unop.thickening).hom.toLinearMap

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators
