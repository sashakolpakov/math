import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SupportPrime
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs
import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductQuotientPrime

/-! # Pair Support Kernel -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Affine.PairSupportKernel.Constructions.Prime

/-! The genuine reduced product support has the actual sum of the
two extended affine prime ideals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SupportPrime.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.CoordinateMaps
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalQuotient OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductQuotientPrime.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem mem_product_zeroLocus (R S : Type) [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
    (I : Ideal R) (J : Ideal S) (q : PrimeSpectrum (R ⊗[ℂ] S)) :
    q ∈ PrimeSpectrum.zeroLocus (TorAlgebra.ExternalQuotient.productIdeal ℂ R S I J : Set (R ⊗[ℂ] S)) ↔
      q.comap (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] S).toRingHom ∈ PrimeSpectrum.zeroLocus (I : Set R) ∧
      q.comap (Algebra.TensorProduct.includeRight : S →ₐ[ℂ] R ⊗[ℂ] S).toRingHom ∈ PrimeSpectrum.zeroLocus (J : Set S) := by
  change J.map _ ⊔ I.map _ ≤ q.asIdeal ↔ I ≤ q.asIdeal.comap _ ∧ J ≤ q.asIdeal.comap _
  rw [sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  exact and_comm

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [IsAffine Y.left] [LocallyOfFiniteType X.hom]
  (A : IrreducibleCloseds X.left) (B : IrreducibleCloseds Y.left)

def affinePairSupport : IrreducibleCloseds (pullback X.hom Y.hom : Scheme) :=
  Geometric.StratumClosure.integralImageClosure (Product.SupportScheme.Constructions.productSupportPullbackMap X Y A B)

omit [IsAffine X.left] [IsAffine Y.left] in
theorem affinePairSupport_coe : (affinePairSupport X Y A B : Set (pullback X.hom Y.hom : Scheme)) =
    pullback.fst X.hom Y.hom ⁻¹' (A : Set X.left) ∩ pullback.snd X.hom Y.hom ⁻¹' (B : Set Y.left) := by
  change closure (Set.range (Product.SupportScheme.Constructions.productSupportPullbackMap X Y A B)) = _
  rw [(Product.SupportScheme.Constructions.productSupportPullbackMap X Y A B).isClosedEmbedding.isClosed_range.closure_eq, Product.SupportScheme.Constructions.productSupportPullbackMap_range]

def affinePairIdeal : Ideal (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)) :=
  TorAlgebra.ExternalQuotient.productIdeal ℂ Γ(X.left, ⊤) Γ(Y.left, ⊤)
    (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X (IntersectionGeometry.supportPoint A)).asIdeal (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap Y (IntersectionGeometry.supportPoint B)).asIdeal

theorem affinePairSupport_zeroLocus :
    (affinePairSupport X Y A B : Set (pullback X.hom Y.hom : Scheme)) =
      (ProductIs.Constructions.affineProductCoordinateIso X Y).hom ⁻¹' PrimeSpectrum.zeroLocus (affinePairIdeal X Y A B : Set (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤))) := by
  rw [affinePairSupport_coe, SupportPrime.Constructions.support_preimage_zeroLocus (CommRingCat.of Γ(X.left, ⊤)) X.left X.left.isoSpec A,
    SupportPrime.Constructions.support_preimage_zeroLocus (CommRingCat.of Γ(Y.left, ⊤)) Y.left Y.left.isoSpec B]
  ext z
  have hf : ((ProductIs.Constructions.affineProductCoordinateIso X Y).hom z).comap
      (Algebra.TensorProduct.includeLeft : Γ(X.left, ⊤) →ₐ[ℂ] Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)).toRingHom =
      ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X (pullback.fst X.hom Y.hom z) :=
    congrArg (fun f : pullback X.hom Y.hom ⟶ Spec (CommRingCat.of Γ(X.left, ⊤)) => f z) (ProductIs.Constructions.CoordinateMaps.coordinateIso_first X Y)
  have hg : ((ProductIs.Constructions.affineProductCoordinateIso X Y).hom z).comap
      (Algebra.TensorProduct.includeRight : Γ(Y.left, ⊤) →ₐ[ℂ] Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)).toRingHom =
      ProductIs.Constructions.CoordinateMaps.affineCoordinateMap Y (pullback.snd X.hom Y.hom z) :=
    congrArg (fun f : pullback X.hom Y.hom ⟶ Spec (CommRingCat.of Γ(Y.left, ⊤)) => f z) (ProductIs.Constructions.CoordinateMaps.coordinateIso_second X Y)
  change (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X (pullback.fst X.hom Y.hom z) ∈ PrimeSpectrum.zeroLocus
      ((ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X (IntersectionGeometry.supportPoint A)).asIdeal : Set Γ(X.left, ⊤)) ∧
    ProductIs.Constructions.CoordinateMaps.affineCoordinateMap Y (pullback.snd X.hom Y.hom z) ∈ PrimeSpectrum.zeroLocus
      ((ProductIs.Constructions.CoordinateMaps.affineCoordinateMap Y (IntersectionGeometry.supportPoint B)).asIdeal : Set Γ(Y.left, ⊤))) ↔ _
  rw [← hf, ← hg]
  exact (mem_product_zeroLocus Γ(X.left, ⊤) Γ(Y.left, ⊤)
    (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X (IntersectionGeometry.supportPoint A)).asIdeal (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap Y (IntersectionGeometry.supportPoint B)).asIdeal
    ((ProductIs.Constructions.affineProductCoordinateIso X Y).hom z)).symm

theorem affinePairIdeal_prime : (affinePairIdeal X Y A B).IsPrime := by
  let : Algebra.FiniteType ℂ Γ(X.left, ⊤) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.affineOverGamma_finiteType X
  let : (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X (IntersectionGeometry.supportPoint A)).asIdeal.IsPrime := (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X (IntersectionGeometry.supportPoint A)).isPrime
  let : (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap Y (IntersectionGeometry.supportPoint B)).asIdeal.IsPrime := (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap Y (IntersectionGeometry.supportPoint B)).isPrime
  exact Tensor.ProductQuotientPrime.Constructions.productIdeal_prime ℂ Γ(X.left, ⊤) Γ(Y.left, ⊤) _ _

theorem affinePairSupport_prime :
    ((ProductIs.Constructions.affineProductCoordinateIso X Y).hom (IntersectionGeometry.supportPoint (affinePairSupport X Y A B))).asIdeal = affinePairIdeal X Y A B := by
  have h := (SupportPrime.Constructions.support_preimage_zeroLocus (CommRingCat.of (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)))
    (pullback X.hom Y.hom) (ProductIs.Constructions.affineProductCoordinateIso X Y) (affinePairSupport X Y A B)).symm.trans
      (affinePairSupport_zeroLocus X Y A B)
  have he := Set.preimage_injective.mpr (ProductIs.Constructions.affineProductCoordinateIso X Y).hom.surjective h
  have hp := affinePairIdeal_prime X Y A B
  exact (((ProductIs.Constructions.affineProductCoordinateIso X Y).hom (IntersectionGeometry.supportPoint (affinePairSupport X Y A B))).isPrime.isRadical.radical).symm.trans
    ((PrimeSpectrum.zeroLocus_eq_iff.mp he).trans hp.isRadical.radical)

end AlgebraicGeometry.CycleClass.Thom.Affine.PairSupportKernel.Constructions.Prime

namespace AlgebraicGeometry.CycleClass.Thom.Affine.PairSupportKernel.Constructions

/-! Native affine stalk coordinates identify both original support
quotients and the genuine diagonal product-support quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SupportPrime.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PairSupportKernel.Constructions.Prime OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.CoordinateMaps OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.StalkCoordinates OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalStalk.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem coordinate_support_kernel_at (R : CommRingCat) (X : Scheme) (e : X ≅ Spec R)
    (A : IrreducibleCloseds X) (x : X) (hx : x ∈ (A : Set X))
    (q : PrimeSpectrum R) (hq : e.hom x = q) :
    (StalkPrimeQuotient.Constructions.kernelPrime X A x hx).asIdeal.map (DiagonalStalk.Constructions.stalkCoordinateIsoAt R X e x q hq).hom.hom =
      (e.hom (IntersectionGeometry.supportPoint A)).asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)) := by
  cases hq
  exact SupportPrime.Constructions.coordinate_support_kernel R X e A x hx

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]

def affineSupportStalkIso (x : X.left) :
    X.left.presheaf.stalk x ≅ CommRingCat.of (Localization.AtPrime (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x).asIdeal) :=
  ProductIs.Constructions.StalkCoordinates.stalkCoordinateIso (CommRingCat.of Γ(X.left, ⊤)) X.left X.left.isoSpec x

theorem affine_support_kernel (A : IrreducibleCloseds X.left) (x : X.left) (hx : x ∈ (A : Set X.left)) :
    (StalkPrimeQuotient.Constructions.kernelPrime X.left A x hx).asIdeal.map (affineSupportStalkIso X x).hom.hom =
      (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X (IntersectionGeometry.supportPoint A)).asIdeal.map
        (algebraMap Γ(X.left, ⊤) (Localization.AtPrime (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x).asIdeal)) :=
  SupportPrime.Constructions.coordinate_support_kernel (CommRingCat.of Γ(X.left, ⊤)) X.left X.left.isoSpec A x hx

variable [LocallyOfFiniteType X.hom] (A B : IrreducibleCloseds X.left)

omit [IsAffine X.left] in
theorem diagonal_mem_affinePairSupport (x : X.left) (hxA : x ∈ (A : Set X.left)) (hxB : x ∈ (B : Set X.left)) :
    pullback.diagonal X.hom x ∈ (Prime.affinePairSupport X X A B : Set (pullback X.hom X.hom : Scheme)) := by
  rw [Prime.affinePairSupport_coe]
  change pullback.fst X.hom X.hom (pullback.diagonal X.hom x) ∈ (A : Set X.left) ∧
    pullback.snd X.hom X.hom (pullback.diagonal X.hom x) ∈ (B : Set X.left)
  have hf : pullback.fst X.hom X.hom (pullback.diagonal X.hom x) = x :=
    congrArg (fun f : X.left ⟶ X.left => f x) (pullback.diagonal_fst X.hom)
  have hg : pullback.snd X.hom X.hom (pullback.diagonal X.hom x) = x :=
    congrArg (fun f : X.left ⟶ X.left => f x) (pullback.diagonal_snd X.hom)
  rw [hf, hg]
  exact ⟨hxA, hxB⟩

theorem affine_pair_support_kernel (x : X.left) (hxA : x ∈ (A : Set X.left)) (hxB : x ∈ (B : Set X.left)) :
    (StalkPrimeQuotient.Constructions.kernelPrime (pullback X.hom X.hom) (Prime.affinePairSupport X X A B) (pullback.diagonal X.hom x)
      (diagonal_mem_affinePairSupport X A B x hxA hxB)).asIdeal.map (DiagonalStalk.Constructions.diagonalStalkIso X x).hom.hom =
        (Prime.affinePairIdeal X X A B).map (algebraMap (Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤))
          (Localization.AtPrime (DiagonalStalk.Constructions.diagonalCoordinatePrime X x).asIdeal)) := by
  have h := coordinate_support_kernel_at (CommRingCat.of (Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤)))
    (pullback X.hom X.hom) (ProductIs.Constructions.affineProductCoordinateIso X X) (Prime.affinePairSupport X X A B)
    (pullback.diagonal X.hom x) (diagonal_mem_affinePairSupport X A B x hxA hxB)
    (DiagonalStalk.Constructions.diagonalCoordinatePrime X x) (DiagonalStalk.Constructions.coordinate_diagonal_point X x)
  rw [Prime.affinePairSupport_prime] at h
  exact h

end AlgebraicGeometry.CycleClass.Thom.Affine.PairSupportKernel.Constructions

end

end OAI
