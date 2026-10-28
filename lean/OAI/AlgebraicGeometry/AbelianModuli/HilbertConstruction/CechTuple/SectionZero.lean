/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionAlternation

/-! # Section Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionZero

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- The zero tuple-chain map does not enlarge support. -/
theorem cechTupleSupportNonincreasing_zero
    {ι : Type u} {n m : ℕ} :
    FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing
      (0 : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m) := by
  intro i
  change FreeCech.TupleChains.CechTupleChain.SupportedBy 0 (Set.range i)
  exact FreeCech.TupleChains.CechTupleChain.supportedBy_zero

/-- The restriction lift sends the zero tuple-chain map to zero. -/
theorem coefficientCechTupleMapF_zero
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n m : ℕ) :
    SectionMaps.coefficientCechTupleMapF coefficientMap M U
        (0 : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m)
        cechTupleSupportNonincreasing_zero = 0 := by
  apply SectionIdentity.coefficientCechHom_ext coefficientMap M U n
  intro i
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n q) i
  calc
    SectionMaps.coefficientCechTupleMapF coefficientMap M U 0
          cechTupleSupportNonincreasing_zero ≫ p =
        SectionMaps.coefficientCechTupleMapComponent coefficientMap M U 0
          cechTupleSupportNonincreasing_zero i := by
      dsimp only [p]
      exact SectionMaps.coefficientCechTupleMapF_comp_π coefficientMap M U 0
        cechTupleSupportNonincreasing_zero i
    _ = 0 := by
      change SectionRows.coefficientCechTupleRow coefficientMap M U i
        ((0 : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m)
          (Finsupp.single i 1)) = 0
      simp
    _ = 0 ≫ p := by simp

/-- Equal support-nonincreasing tuple maps have equal restriction lifts. -/
theorem coefficientCechTupleMapF_congr
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f g : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m)
    (hf : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f)
    (hg : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing g) (hfg : f = g) :
    SectionMaps.coefficientCechTupleMapF coefficientMap M U f hf =
      SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg := by
  subst g
  rfl

/-- The tuple homotopy identity as an equality of integral linear maps. -/
theorem cechTupleAlternatingHomotopy_linear_identity
    {ι : Type u} [LinearOrder ι] (n : ℕ) :
    (FreeCech.TupleChains.cechTupleBoundary n).comp
          (FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n) +
        FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious n =
      FreeCech.TupleAlternation.cechTupleAlternatingProjection n +
        -(LinearMap.id :
          FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι n) := by
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.neg_apply, LinearMap.id_apply, sub_eq_add_neg]
    using FreeCech.TupleHomotopyIdentity.cechTupleAlternatingHomotopy_identity n x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionZero
