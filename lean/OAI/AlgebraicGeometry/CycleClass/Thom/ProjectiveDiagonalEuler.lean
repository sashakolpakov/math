import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations

/-! # Projective Diagonal Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDiagonalEuler.Constructions

noncomputable section

/-! The original projective support Tor Euler sum equals the Euler
sum for its actual product support and the constructed diagonal germs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport.Constructions.Restriction OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportEuler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEuler.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PairSupportKernel.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PairSupportKernel.Constructions.Prime OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEquations.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.Local.QuotientEulerEquiv.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (j : X ⟶ V.toOver)
  [IsAffine X.left] [IsOpenImmersion j.left] [LocallyOfFiniteType X.hom]
  (p q : ℕ) (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)

omit [IsAffine X.left] [LocallyOfFiniteType X.hom] [IsOpenImmersion j.left] in
theorem pair_center_mem (x : X.left) (hxA : j.left x ∈ (A.val : Set V.carrier))
    (hxB : j.left x ∈ (B.val : Set V.carrier)) :
    Diagonal.OpenEquations.Constructions.center V X j x ∈ ((Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B).val : Set (Diagonal.Ambient.Constructions.productVariety V V).carrier) := by
  change Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j (pullback.diagonal X.hom x) ∈ _
  rw [Diagonal.OpenNeighborhood.Constructions.diagonal_point]
  exact (congrArg (fun S : Set V.carrier => j.left x ∈ S) (Diagonal.Ambient.Constructions.diagonal_product_preimage V p q A B)).mpr ⟨hxA, hxB⟩

variable (hA : IntersectionGeometry.supportPoint A.val ∈ Set.range j.left) (hB : IntersectionGeometry.supportPoint B.val ∈ Set.range j.left)
  (x : X.left) (hxA : j.left x ∈ (A.val : Set V.carrier)) (hxB : j.left x ∈ (B.val : Set V.carrier))

omit [IsAffine X.left] in
include hxA hxB in
theorem source_center_mem : pullback.diagonal X.hom x ∈
    (Product.SupportOpen.Constructions.sourcePairSupport V X j p q A B hA hB : Set (pullback X.hom X.hom : Scheme)) :=
  Affine.PairSupportKernel.Constructions.diagonal_mem_affinePairSupport X (Open.StalkSupport.Constructions.Restriction.restrictedSupport j.left A.val hA) (Open.StalkSupport.Constructions.Restriction.restrictedSupport j.left B.val hB) x
    (Open.StalkSupport.Constructions.Restriction.restrictedSupport_mem j.left A.val hA x hxA) (Open.StalkSupport.Constructions.Restriction.restrictedSupport_mem j.left B.val hB x hxB)

variable (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

omit [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] in
theorem product_open_euler (d : ℕ) :
    TorAlgebra.Euler.Tor.euler (Diagonal.OpenEquations.Constructions.ambientLocalRing V X j x)
      (ModuleCat.of _ ((Diagonal.OpenEquations.Constructions.ambientLocalRing V X j x) ⧸ Ideal.ofList (Diagonal.OpenEquations.Constructions.diagonalGerms V X j n x)))
      (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing (Diagonal.Ambient.Constructions.productVariety V V).carrier (Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B).val
        (Diagonal.OpenEquations.Constructions.center V X j x) (pair_center_mem V X j p q A B x hxA hxB))) d =
    TorAlgebra.Euler.Tor.euler (Affine.DiagonalEquations.Constructions.productLocalRing X x)
      (ModuleCat.of _ ((Affine.DiagonalEquations.Constructions.productLocalRing X x) ⧸ Ideal.ofList (Affine.DiagonalEquations.Constructions.coordinateDifferenceGerms X n x)))
      (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing (pullback X.hom X.hom) (Product.SupportOpen.Constructions.sourcePairSupport V X j p q A B hA hB)
        (pullback.diagonal X.hom x) (source_center_mem V X j p q A B hA hB x hxA hxB))) d := by
  let f := (Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j).stalkMap (pullback.diagonal X.hom x)
  have h := Local.QuotientEulerEquiv.Constructions.euler_quotients_ringEquiv (Diagonal.OpenEquations.Constructions.ambientLocalRing V X j x) (Affine.DiagonalEquations.Constructions.productLocalRing X x)
    (asIso f).commRingCatIsoToRingEquiv (Ideal.ofList (Diagonal.OpenEquations.Constructions.diagonalGerms V X j n x))
    (StalkPrimeQuotient.Constructions.kernelPrime (Diagonal.Ambient.Constructions.productVariety V V).carrier (Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B).val
      (Diagonal.OpenEquations.Constructions.center V X j x) (pair_center_mem V X j p q A B x hxA hxB)).asIdeal d
  have hI : (Ideal.ofList (Diagonal.OpenEquations.Constructions.diagonalGerms V X j n x)).map f.hom = Ideal.ofList (Affine.DiagonalEquations.Constructions.coordinateDifferenceGerms X n x) := by
    rw [Ideal.map_ofList]
    exact congrArg Ideal.ofList (Diagonal.OpenEquations.Constructions.diagonalGerms_map V X j n x)
  have hJ := Open.StalkSupport.Constructions.kernelPrime_map (Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j) (Product.SupportOpen.Constructions.sourcePairSupport V X j p q A B hA hB)
    (Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B).val (Product.SupportOpen.Constructions.pair_support_genericPoint V X j p q A B hA hB)
    (pullback.diagonal X.hom x) (source_center_mem V X j p q A B hA hB x hxA hxB)
    (pair_center_mem V X j p q A B x hxA hxB)
  exact h.trans (Local.QuotientEulerEquiv.Constructions.euler_quotients_congr _ _ _ _ _ hI hJ d)

include hA hB in
theorem projective_diagonal_euler
    [Algebra.FormallyUnramified (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
    [IsNoetherianRing (Γ(X.left, ⊤) ⊗[MvPolynomial (Fin n) ℂ] Γ(X.left, ⊤))] (d : ℕ) :
    TorAlgebra.Euler.Tor.euler (V.carrier.presheaf.stalk (j.left x))
      (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier A.val (j.left x) hxA))
      (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier B.val (j.left x) hxB)) d =
    TorAlgebra.Euler.Tor.euler (Diagonal.OpenEquations.Constructions.ambientLocalRing V X j x)
      (ModuleCat.of _ ((Diagonal.OpenEquations.Constructions.ambientLocalRing V X j x) ⧸ Ideal.ofList (Diagonal.OpenEquations.Constructions.diagonalGerms V X j n x)))
      (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing (Diagonal.Ambient.Constructions.productVariety V V).carrier (Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B).val
        (Diagonal.OpenEquations.Constructions.center V X j x) (pair_center_mem V X j p q A B x hxA hxB))) d := by
  let C := Open.StalkSupport.Constructions.Restriction.restrictedSupport j.left A.val hA
  let D := Open.StalkSupport.Constructions.Restriction.restrictedSupport j.left B.val hB
  have hxC := Open.StalkSupport.Constructions.Restriction.restrictedSupport_mem j.left A.val hA x hxA
  have hxD := Open.StalkSupport.Constructions.Restriction.restrictedSupport_mem j.left B.val hB x hxB
  have h := Open.SupportEuler.Constructions.open_support_euler j.left C D A.val B.val
    (Open.StalkSupport.Constructions.Restriction.restrictedSupport_genericPoint j.left A.val hA) (Open.StalkSupport.Constructions.Restriction.restrictedSupport_genericPoint j.left B.val hB)
    x hxC hxD hxA hxB d
  exact h.trans ((Affine.DiagonalEuler.Constructions.affine_diagonal_euler X C D x hxC hxD n d).trans
    (product_open_euler V X j p q A B hA hB x hxA hxB n d).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDiagonalEuler.Constructions
