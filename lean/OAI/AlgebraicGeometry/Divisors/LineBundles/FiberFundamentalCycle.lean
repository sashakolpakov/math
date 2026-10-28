import OAI.AlgebraicGeometry.Divisors.LineBundles.Ord
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Fiber Fundamental Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiberFundamentalCycle.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual finite fiber cycles, with all irreducible components and local-ring multiplicities -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

def componentGenericPoint (X : Scheme.{0}) (C : irreducibleComponents X) : X :=
  irreducibleSetEquivPoints ⟨C.val, C.property.1, isClosed_of_mem_irreducibleComponents _ C.property⟩

theorem componentGenericPoint_coheight (X : Scheme.{0}) (C : irreducibleComponents X) :
    coheight (componentGenericPoint X C) = 0 := by
  apply IsMax.coheight_eq_zero
  apply (irreducibleSetEquivPoints.isMax_apply).mpr
  intro W hW
  exact C.property.2 W.isIrreducible hW

theorem componentGenericPoint_length_finite (X : Scheme.{0}) [IsLocallyNoetherian X]
    (C : irreducibleComponents X) :
    Module.length (X.presheaf.stalk (componentGenericPoint X C))
      (X.presheaf.stalk (componentGenericPoint X C)) ≠ ⊤ := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk (componentGenericPoint X C)) :=
    krullDimLE_of_coheight_le (componentGenericPoint_coheight X C).le
  have : IsArtinianRing (X.presheaf.stalk (componentGenericPoint X C)) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  exact Module.length_ne_top

variable {X Y : Scheme.{0}} (p : X ⟶ Y) [LocallyOfFiniteType p] [QuasiCompact p]

instance finiteTypeFiber_isNoetherian (y : Y) : AlgebraicGeometry.IsNoetherian (p.fiber y) := by
  have : LocallyOfFiniteType (p.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd p (Y.fromSpecResidueField y)))
  have : IsLocallyNoetherian (p.fiber y) := LocallyOfFiniteType.isLocallyNoetherian (p.fiberToSpecResidueField y)
  exact ⟨⟩

def fiberFundamentalPointCycle (y : Y) : X →₀ ℚ := by
  let := (NoetherianSpace.finite_irreducibleComponents (α := p.fiber y)).fintype
  exact ∑ C : irreducibleComponents (p.fiber y),
    Finsupp.single (p.fiberι y (componentGenericPoint (p.fiber y) C))
      ((Module.length ((p.fiber y).presheaf.stalk (componentGenericPoint (p.fiber y) C))
        ((p.fiber y).presheaf.stalk (componentGenericPoint (p.fiber y) C))).toNat : ℚ)

/-- On a flat finite-type morphism this is the usual pullback of finite cycles:
the fiber's actual generic points, weighted by the lengths of their local rings. -/
def fiberPointCyclePullback : (Y →₀ ℚ) →ₗ[ℚ] (X →₀ ℚ) :=
  Finsupp.linearCombination ℚ (fiberFundamentalPointCycle p)

theorem fiberPointCyclePullback_single (y : Y) (a : ℚ) :
    fiberPointCyclePullback p (Finsupp.single y a) = a • fiberFundamentalPointCycle p y :=
  Finsupp.linearCombination_single ℚ a y

end

/-! Every actual generic local ring of a reduced scheme has length one. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem componentGenericPoint_length_one_of_reduced (X : Scheme.{0}) [IsReduced X]
    (C : irreducibleComponents X) :
    Module.length (X.presheaf.stalk (componentGenericPoint X C))
      (X.presheaf.stalk (componentGenericPoint X C)) = 1 := by
  have hx : closure {componentGenericPoint X C} = C.val :=
    C.property.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents _ C.property)
  have hf : IsField (X.presheaf.stalk (componentGenericPoint X C)) :=
    isField_stalk_of_closure_mem_irreducibleComponents X _ (hx.symm ▸ C.property)
  let := hf.toField
  exact Module.length_eq_one _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiberFundamentalCycle.BundleCycles
