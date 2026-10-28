import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.DeRhamMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameLinearization

/-! # Linearization -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Linearization.CrystallineFrameLinearization

noncomputable section

/-!
# Native frame-resolution terms are scalar extensions of ordinary forms

The actual divided-coordinate ambient rings are algebras over the fixed
polynomial frame, naturally in crystalline morphisms. In every degree,
extending the actual ordinary polynomial forms to this ambient ring gives
the corresponding term of the native crystalline frame resolution.
-/

open _root_.CategoryTheory Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "P" => MvPolynomial σ W

/-- The native frame-extension ring, with its fixed polynomial algebra structure. -/
def Ring (_a : σ → B) (Q : C) : Type u :=
  DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)

variable (a : σ → B)
variable (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))

instance ringCommRing : CommRing (Ring p k B σ a Q) :=
  inferInstanceAs (CommRing (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)))

instance ringWittAlgebra : Algebra W (Ring p k B σ a Q) :=
  inferInstanceAs (Algebra W (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)))

instance ringFrameAlgebra : Algebra P (Ring p k B σ a Q) :=
  (Functor.CrystallineFrameFunctor.polynomialMap a Q).toRingHom.toAlgebra

instance ringTower : IsScalarTower W P (Ring p k B σ a Q) :=
  IsScalarTower.of_algebraMap_eq' (Functor.CrystallineFrameFunctor.polynomialMap a Q).comp_algebraMap.symm

variable {p k B σ}
variable {T U : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)}

def ringMap (f : T ⟶ U) : Ring p k B σ a U →ₐ[MvPolynomial σ (WittVector p k)] Ring p k B σ a T where
  __ := (Map.CrystallineFrameMap.ambientMap a f).toRingHom
  commutes' t := DFunLike.congr_fun (Functor.CrystallineFrameFunctor.polynomialMap_naturality a f) t

variable (p k B σ)

abbrev term (n : ℕ) := (Ring p k B σ a Q) ⊗[P] DeRhamPresentationTo.DeRhamPresentation.Form W P n

/-- The target is an actual term of the native frame-coordinate complex. -/
def termIso [Fintype σ] (n : ℕ) : ModuleCat.of W (term p k B σ a Q n) ≅
    (Koszul.Functor.KoszulFunctor.object W σ (Operators.CrystallineFrameOperators.functions p k B σ a)
      (Operators.CrystallineFrameOperators.derivative p k B σ a)
      (Resolution.CrystallineFrameResolution.commute p k B σ a) (op Q)).X n := by
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact ((Polynomial.FrameLinearization.PolynomialFrameLinearization.termEquiv W σ (Ring p k B σ a Q) n).restrictScalars W).toModuleIso

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Linearization.CrystallineFrameLinearization
