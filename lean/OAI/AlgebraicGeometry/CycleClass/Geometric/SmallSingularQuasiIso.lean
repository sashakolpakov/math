import OAI.AlgebraicGeometry.CycleClass.Geometric.EventuallySmall
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivisionHomotopy
import OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion

/-! # Small Singular Quasi Iso -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSingularQuasiIso.Cycles

noncomputable section

/-!
# The actual open-cover small-chain inclusion is a quasi-isomorphism

This module applies the eventual-smallness criterion to the constructed signed
barycentric subdivision chain maps and their constructed chain homotopies.
The only hypotheses are that the given family consists of open subsets and
covers the actual topological space.
-/

open _root_.CategoryTheory

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)

/-- For an actual open cover, the canonical inclusion of cover-small integral
singular chains into all integral singular chains is a quasi-isomorphism. -/
theorem smallIntegralChainInclusion_quasiIso
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    _root_.QuasiIso (SmallChainImage.Cycles.smallIntegralChainInclusion X U) :=
  EventuallySmall.Cycles.quasiIso_of_eventuallySmall
    (SmallChainImage.Cycles.smallIntegralChainInclusion X U)
    (SmallChainImage.Cycles.smallIntegralChainInclusion_injective X U)
    (SmallSubdivision.Cycles.smallSubdivisionChainMap X U)
    (SubdivisionBoundary.Cycles.subdivisionChainMap X)
    (SmallSubdivision.Cycles.smallSubdivisionChainMap_intertwining X U)
    (SmallSubdivisionHomotopy.Cycles.smallSubdivisionHomotopy X U)
    (SubdivisionHomotopy.Cycles.subdivisionHomotopy X)
    (fun _ c => SmallSubdivision.Cycles.exists_subdivisionChainMap_iterate_small_preimage X U hopen hcover c)

/-- The induced homology map is bijective in every degree, including zero. -/
theorem smallIntegralHomologyMap_bijective
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap (SmallChainImage.Cycles.smallIntegralChainInclusion X U) n) := by
  let _ := smallIntegralChainInclusion_quasiIso X U hopen hcover
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- The genuine homology isomorphism induced by the canonical inclusion of
open-cover small singular chains. -/
def smallIntegralHomologyIso
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (SmallChainImage.Cycles.integralSmallSingularChains X U).homology n ≅ (LocalHomology.Cycles.integralSingularChains X).homology n := by
  letI := smallIntegralChainInclusion_quasiIso X U hopen hcover
  exact isoOfQuasiIsoAt (SmallChainImage.Cycles.smallIntegralChainInclusion X U) n

@[simp]
theorem smallIntegralHomologyIso_hom
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (smallIntegralHomologyIso X U hopen hcover n).hom =
      HomologicalComplex.homologyMap (SmallChainImage.Cycles.smallIntegralChainInclusion X U) n := rfl

@[reassoc (attr := simp)]
theorem smallIntegralHomologyMap_iso_inv
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    HomologicalComplex.homologyMap (SmallChainImage.Cycles.smallIntegralChainInclusion X U) n ≫
      (smallIntegralHomologyIso X U hopen hcover n).inv = 𝟙 _ :=
  (smallIntegralHomologyIso X U hopen hcover n).hom_inv_id

@[reassoc (attr := simp)]
theorem smallIntegralHomologyIso_inv_map
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (smallIntegralHomologyIso X U hopen hcover n).inv ≫
      HomologicalComplex.homologyMap (SmallChainImage.Cycles.smallIntegralChainInclusion X U) n = 𝟙 _ :=
  (smallIntegralHomologyIso X U hopen hcover n).inv_hom_id

variable (A B : Set X)

/-- Actual quasi-isomorphism for a binary open cover, in the presentation used
by the small-chain Mayer--Vietoris sequence. -/
theorem binarySmallIntegralChainInclusion_quasiIso
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    _root_.QuasiIso (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B) := by
  have hopen : ∀ b : Bool, IsOpen (if b then B else A) := by
    intro b
    cases b
    · exact hA
    · exact hB
  have hcov : ∀ x : X, ∃ b : Bool, x ∈ if b then B else A := by
    intro x
    have hx : x ∈ A ∪ B := by rw [hcover]; trivial
    rcases hx with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  let _ := smallIntegralChainInclusion_quasiIso X
    (fun b : Bool => if b then B else A) hopen hcov
  dsimp only [BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion]
  infer_instance

/-- The binary-cover small homology is canonically the ambient singular
homology for an actual binary open cover. -/
def binarySmallIntegralHomologyIso
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) (n : ℕ) :
    SmallMayerVietoris.Cycles.binarySmallSingularHomology X A B n ≅ (LocalHomology.Cycles.integralSingularChains X).homology n := by
  letI := binarySmallIntegralChainInclusion_quasiIso X A B hA hB hcover
  exact isoOfQuasiIsoAt (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B) n

@[simp]
theorem binarySmallIntegralHomologyIso_hom
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) (n : ℕ) :
    (binarySmallIntegralHomologyIso X A B hA hB hcover n).hom =
      HomologicalComplex.homologyMap (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B) n := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSingularQuasiIso.Cycles
