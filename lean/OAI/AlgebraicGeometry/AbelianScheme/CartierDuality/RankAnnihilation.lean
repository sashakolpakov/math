import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HopfShear
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroups
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Rank Annihilation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RankAnnihilation.Construction.NormCharacters

noncomputable section

/-!
# CartierDuality: the rank annihilates the full finite-free commutative group

Cartier biduality turns the norm calculation for characters into an
identity of the actual affine group-scheme morphisms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.CategoryTheory.MonObj

universe u v w

/-- Precomposition by a bialgebra map respects the convolution law. -/
def convPrecomp {R A B S : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing S]
    [Bialgebra R A] [Bialgebra R B] [Algebra R S] (f : B →ₐc[R] A) :
    WithConv (A →ₐ[R] S) →* WithConv (B →ₐ[R] S) where
  toFun x := WithConv.toConv (x.ofConv.comp f.toAlgHom)
  map_one' := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    exact congrArg (algebraMap R S) (CoalgHomClass.counit_comp_apply f b)
  map_mul' x y := congrArg WithConv.toConv (AlgHom.convMul_comp_bialgHom_distrib x y f)

variable (R : Type u) [CommRing R]
variable (A : Type u) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
variable [Module.Finite R A] [Module.Projective R A]

local instance : CommRing (DualAlgebra.Construction.DualCoordinate R A) := LinearMap.convCommRing
local instance : Algebra R (DualAlgebra.Construction.DualCoordinate R A) := LinearMap.convAlgebra
local instance : CommRing (DualAlgebra.Construction.DualCoordinate R (DualAlgebra.Construction.DualCoordinate R A)) := LinearMap.convCommRing
local instance : Algebra R (DualAlgebra.Construction.DualCoordinate R (DualAlgebra.Construction.DualCoordinate R A)) := LinearMap.convAlgebra

/-- An arbitrary algebra-valued point is killed by the finite-free rank;
this retains nonreduced test algebras. -/
theorem point_pow_card {I : Type*} [Fintype I] (b : Module.Basis I R A)
    (S : Type w) [CommRing S] [Algebra R S] (x : WithConv (A →ₐ[R] S)) :
    x ^ Fintype.card I = 1 := by
  classical
  let d := DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R A
  let y : WithConv (DualAlgebra.Construction.DualCoordinate R (DualAlgebra.Construction.DualCoordinate R A) →ₐ[R] S) :=
    WithConv.toConv (x.ofConv.comp d.symm.toAlgEquiv.toAlgHom)
  let e := CharacterGroups.Construction.affineDualPointsMulEquivCharacters R S (DualAlgebra.Construction.DualCoordinate R A)
  let bd : Module.Basis I R (DualAlgebra.Construction.DualCoordinate R A) :=
    b.dualBasis.map (DualAlgebra.Construction.dualCoordinateLinearEquiv R A).symm
  have hy : y ^ Fintype.card I = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact HopfShear.Construction.NormCharacters.groupLike_pow_card S (S ⊗[R] DualAlgebra.Construction.DualCoordinate R A) (bd.baseChange S) (e y)
  have hxy : convPrecomp d.toBialgHom y = x := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    change x.ofConv (d.symm (d a)) = x.ofConv a
    rw [d.symm_apply_apply]
  have h := congrArg (convPrecomp d.toBialgHom) hy
  rwa [map_pow, map_one, hxy] at h

/-- Multiplication by the rank is the trivial morphism of the actual
finite-free affine commutative group scheme. -/
theorem affineGroup_power_card {I : Type*} [Fintype I] (b : Module.Basis I R A) :
    (𝟙 ((Spec (.of A)).asOver (Spec (.of R)))) ^ Fintype.card I =
      (1 : (Spec (.of A)).asOver (Spec (.of R)) ⟶ (Spec (.of A)).asOver (Spec (.of R))) := by
  let x : WithConv (A →ₐ[R] A) := WithConv.toConv (AlgHom.id R A)
  have hx : Spec.mapMulEquiv (R := R) (S := A) (T := A) x =
      𝟙 ((Spec (.of A)).asOver (Spec (.of R))) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (RingHom.id A)) = 𝟙 _
    exact Spec.map_id _
  have h := congrArg (Spec.mapMulEquiv (R := R) (S := A) (T := A)) (point_pow_card R A b A x)
  rwa [map_pow, map_one, hx] at h

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RankAnnihilation.Construction.NormCharacters
