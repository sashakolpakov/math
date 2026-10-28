import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNeighborhood
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.RangeSectionPullback
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap

/-! # Open Equations -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations.Constructions

noncomputable section

/-! Coordinate differences as actual sections on a literal open of
the smooth projective self-product. Their native germs are regular,
lie in the maximal ideal, and generate the original diagonal ideal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Support.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.RangeSectionPullback.Constructions.Sections
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalSupportKernel.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (j : X ⟶ V.toOver)
  [IsAffine X.left] [IsIntegral X.left] [IsOpenImmersion j.left]

def productOpen : (Ambient.Constructions.productVariety V V).carrier.Opens := (OpenNeighborhood.Constructions.productOpenMap V X j).opensRange

abbrev center (x : X.left) : (Ambient.Constructions.productVariety V V).carrier := OpenNeighborhood.Constructions.productOpenMap V X j (pullback.diagonal X.hom x)

omit [IsAffine X.left] [IsIntegral X.left] in
theorem center_mem (x : X.left) : center V X j x ∈ productOpen V X j := ⟨_, rfl⟩

abbrev ambientLocalRing (x : X.left) : CommRingCat := (Ambient.Constructions.productVariety V V).carrier.presheaf.stalk (center V X j x)

variable (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

def diagonalSection (i : Fin n) : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase (productOpen V X j)).left, ⊤) :=
  Open.RangeSectionPullback.Constructions.Sections.rangeSection (OpenNeighborhood.Constructions.productOpenMap V X j) (Affine.DiagonalEquations.Constructions.coordinateDifferenceSection X n i)

def diagonalGerms (x : X.left) : List (ambientLocalRing V X j x) :=
  Section.StalkMap.Constructions.VectorGerms.vectorGerms (Ambient.Constructions.productVariety V V) (productOpen V X j) (center V X j x) (center_mem V X j x)
    n (diagonalSection V X j n)

omit [IsIntegral X.left] [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] in
theorem diagonalGerms_map (x : X.left) :
    (diagonalGerms V X j n x).map ((OpenNeighborhood.Constructions.productOpenMap V X j).stalkMap (pullback.diagonal X.hom x)).hom =
      Affine.DiagonalEquations.Constructions.coordinateDifferenceGerms X n x := by
  simp only [diagonalGerms, Section.StalkMap.Constructions.VectorGerms.vectorGerms, List.map_ofFn, Function.comp_def, Affine.DiagonalEquations.Constructions.coordinateDifferenceGerms]
  apply congrArg List.ofFn
  funext i
  exact Open.RangeSectionPullback.Constructions.Sections.rangeSection_germ (OpenNeighborhood.Constructions.productOpenMap V X j) (pullback.diagonal X.hom x) (Affine.DiagonalEquations.Constructions.coordinateDifferenceSection X n i)

omit [IsIntegral X.left] [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] in
theorem diagonalGerms_length (x : X.left) : (diagonalGerms V X j n x).length = n := by
  simp only [diagonalGerms, Section.StalkMap.Constructions.VectorGerms.vectorGerms, List.length_map, List.length_ofFn]

omit [IsIntegral X.left] in
theorem diagonalGerms_regular [Module.Flat (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] (x : X.left) :
    IsWeaklyRegular (ambientLocalRing V X j x) (diagonalGerms V X j n x) := by
  let e := (asIso ((OpenNeighborhood.Constructions.productOpenMap V X j).stalkMap (pullback.diagonal X.hom x))).commRingCatIsoToRingEquiv
  have hmap : (diagonalGerms V X j n x).map e = Affine.DiagonalEquations.Constructions.coordinateDifferenceGerms X n x := diagonalGerms_map V X j n x
  have he : IsWeaklyRegular (ambientLocalRing V X j x) (diagonalGerms V X j n x) ↔
      IsWeaklyRegular (Affine.DiagonalEquations.Constructions.productLocalRing X x) ((diagonalGerms V X j n x).map e) :=
    e.toAddEquiv.isWeaklyRegular_congr (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr (fun r _ y => e.map_mul r y)))
  apply he.mpr
  rw [hmap]
  exact Affine.DiagonalEquations.Constructions.coordinateDifferenceGerms_regular X n x

omit [IsIntegral X.left] [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] in
theorem diagonalGerms_maximal (x : X.left) :
    ∀ a ∈ diagonalGerms V X j n x, a ∈ IsLocalRing.maximalIdeal (ambientLocalRing V X j x) := by
  intro a ha
  let f := ((OpenNeighborhood.Constructions.productOpenMap V X j).stalkMap (pullback.diagonal X.hom x)).hom
  have hm : f a ∈ Affine.DiagonalEquations.Constructions.coordinateDifferenceGerms X n x :=
    diagonalGerms_map V X j n x ▸ List.mem_map.mpr ⟨a, ha, rfl⟩
  have h := Affine.DiagonalEquations.Constructions.coordinateDifferenceGerms_maximal X n x (f a) hm
  exact (congrArg (fun I : Ideal (ambientLocalRing V X j x) => a ∈ I) (IsLocalRing.maximalIdeal_comap f)).mp h

theorem diagonalGerms_ideal
    [Algebra.FormallyUnramified (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
    [IsNoetherianRing (Γ(X.left, ⊤) ⊗[MvPolynomial (Fin n) ℂ] Γ(X.left, ⊤))] (x : X.left) :
    Ideal.ofList (diagonalGerms V X j n x) =
      (StalkPrimeQuotient.Constructions.kernelPrime (Ambient.Constructions.productVariety V V).carrier (Support.Constructions.diagonalClosedSupport V)
        (center V X j x) (OpenNeighborhood.Constructions.diagonal_mem V X j x)).asIdeal := by
  let f := ((OpenNeighborhood.Constructions.productOpenMap V X j).stalkMap (pullback.diagonal X.hom x)).hom
  have hm : (Ideal.ofList (diagonalGerms V X j n x)).map f =
      (StalkPrimeQuotient.Constructions.kernelPrime (Ambient.Constructions.productVariety V V).carrier (Support.Constructions.diagonalClosedSupport V)
        (center V X j x) (OpenNeighborhood.Constructions.diagonal_mem V X j x)).asIdeal.map f := by
    rw [Ideal.map_ofList, diagonalGerms_map, OpenNeighborhood.Constructions.diagonal_kernel_map]
    exact Affine.DiagonalSupportKernel.Constructions.coordinateDifferenceGerms_support_ideal X n x
  exact (Ideal.relIsoOfBijective f
    (ConcreteCategory.bijective_of_isIso ((OpenNeighborhood.Constructions.productOpenMap V X j).stalkMap (pullback.diagonal X.hom x)))).symm.injective hm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations.Constructions
