import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareDualData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizationIsogenyGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.LevelGluing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareFixedFactor
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PositivityDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianPolarizedLevelRecovery

/-! # Polarized Family Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedFamilyGluing.DirectedPolarizedSchemeGluing

noncomputable section

/-! Effective descent of the original polarized full-level objects
along a directed open cover. The abelian and dual schemes, Poincare
line, polarization map, and full ordered level are all constructed.
Every chart recovers the given original object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S : Scheme.{0}} (C : S.OpenCover.{0})
  [Category C.I₀] [C.LocallyDirected] [Small.{0} C.I₀] [Quiver.IsThin C.I₀]
  [∀ i, IsLocallyNoetherian (C.X i)] {g N : ℕ} {δ : Fin g → ℕ}
  (F : ∀ i, PolarizationData.PolarizedAbelianWithFullLevel g δ N (C.X i)) (hN : 3 ≤ N)
  (e : ∀ {i j : C.I₀} (f : i ⟶ j), Moduli.Isomorphisms.LevelPreservingIso (F i) ((F j).pullback (C.trans f)))

local notation "A" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e
local notation "E" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualAbelian C F hN e
local notation "D" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareDualData.DirectedPolarizedSchemeGluing.poincareDual C F hN e
local notation "p" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizationIsogenyGluing.DirectedPolarizedSchemeGluing.polarizationMap C F hN e

section LocallyNoetherian

variable [IsLocallyNoetherian S]

/-- The line-recovery map is precisely the original native mixed
product map used in polarization and full-level base change. -/
theorem poincareLine_mixedRecovery (i : C.I₀) :
    Line.Bundles.LineBundle.pullbackClass
      (ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap (C.f i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i))
      (Line.Bundles.LineBundle.classOf (D).poincare) = Line.Bundles.LineBundle.classOf (F i).dual.poincare := by
  have h : PoincareLineObject.DirectedPolarizedSchemeGluing.poincareLineOriginalMap C F hN e i =
      ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap (C.f i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i) :=
    ReferenceFamily.PoincareFixedFactor.fixedFamilyPoincareComparison_factor (F i).dual A (C.f i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i)
      (E).scheme (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i) (PoincareTransitions.DirectedPolarizedSchemeGluing.poincareParameterInclusion C F hN e i)
      ((PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualData C F hN e).chartIso_fst i).symm
  exact (congrArg (fun f => Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.classOf (D).poincare)) h).symm.trans
    (PoincareLineObject.DirectedPolarizedSchemeGluing.poincareLine_originalRecovery C F hN e i)

/-- The original ample geometric-fiber witnesses descend through the
native recovered Poincare formula. -/
theorem polarization_positive (K : Type) [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ S) : PolarizationData.PositiveOnGeometricFiber D p K s := by
  obtain ⟨i, x, hx⟩ := C.exists_eq (s default)
  obtain ⟨a, ha, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (C.f i) s x hx
  have hp := ReferenceFamily.Polarization.PositivityDescent.positiveOnGeometricFiber_cartesian (F i).dual D (C.f i)
    (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i)
    (F i).polarization.isogeny.hom p (PolarizationIsogenyGluing.DirectedPolarizedSchemeGluing.polarizationMap_chart C F hN e i)
    (poincareLine_mixedRecovery C F hN e i) K a ((F i).polarization.positive K a)
  exact ha ▸ hp

/-- The original polarization, including its full kernel type and
geometric positivity; no positivity premise is added. -/
def polarization : PolarizationData.Polarization D δ where
  isogeny := PolarizationIsogenyGluing.DirectedPolarizedSchemeGluing.isogeny C F hN e
  kernelType := PolarizationIsogenyGluing.DirectedPolarizedSchemeGluing.isogeny_type C F hN e
  positive K _ _ s := polarization_positive C F hN e K s

end LocallyNoetherian

variable [IsNoetherian S] [NeZero N]

/-- The descended original polarized abelian scheme with full ordered
level, on the actual glued base. -/
def family : PolarizationData.PolarizedAbelianWithFullLevel g δ N S where
  abelian := A
  dual := D
  polarization := DirectedPolarizedSchemeGluing.polarization C F hN e
  level := LevelGluing.DirectedPolarizedSchemeGluing.level C F hN e

/-- Original chart recovery preserves both group schemes, the actual
Poincare class, the polarization map, and every ordered level label. -/
def familyChartIso (i : C.I₀) :
    Moduli.Isomorphisms.LevelPreservingIso (F i) ((family C F hN e).pullback (C.f i)) := by
  let eA : (F i).abelian.scheme ≅ ((family C F hN e).abelian.pullback (C.f i)).scheme :=
    PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i
  let eD : (F i).dual.abelian.scheme ≅ ((family C F hN e).dual.abelian.pullback (C.f i)).scheme :=
    PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i
  letI : IsMonHom eA.hom := PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso_group C F hN e i
  letI : IsMonHom eD.hom := PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso_group C F hN e i
  exact ReferenceFamily.CartesianPolarizedLevelRecovery.levelIso_of_cartesian_recovery (F i) (family C F hN e) (C.f i) eA eD
    (PolarizationIsogenyGluing.DirectedPolarizedSchemeGluing.polarizationMap_chart C F hN e i) (poincareLine_mixedRecovery C F hN e i)
    (LevelGluing.DirectedPolarizedSchemeGluing.chartIso_level C F hN e i).symm

theorem familyChartIso_abelian (i : C.I₀) :
    (familyChartIso C F hN e i).abelian = PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i := rfl

theorem familyChartIso_dual (i : C.I₀) :
    (familyChartIso C F hN e i).dual = PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i := rfl

/-- Recovery remains an original full moduli isomorphism after every
base change of a chart, including nonreduced and non-Noetherian tests. -/
def familyChartIsoOnTest (i : C.I₀) {T : Scheme.{0}} (t : T ⟶ C.X i) :
    Moduli.Isomorphisms.LevelPreservingIso ((F i).pullback t) ((family C F hN e).pullback (t ≫ C.f i)) :=
  ((familyChartIso C F hN e i).pullback t).trans
    (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp (family C F hN e) (C.f i) t)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedFamilyGluing.DirectedPolarizedSchemeGluing
