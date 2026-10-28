import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricQuotient
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.QuotientRepresentability

/-! # Geometric Quotient Sheaf Cokernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The constructed geometric abelian quotient is the actual cokernel
of its subgroup inclusion in commutative fppf sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.QuotientRepresentability.Construction.Schemes

variable {k : Type u} [Field k] [IsAlgClosed k] {g : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable {H : Grp (Over (Spec (.of k)))} [IsCommMonObj H.X]
variable {i : H.X ⟶ A.scheme} [IsMonHom i] [Mono i]
variable (Q : GeometricQuotient.Construction.GeometricKernelQuotient A H i)

def GeometricQuotient.Construction.GeometricKernelQuotient.commutativeSheafProjection : CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk A.scheme) ⟶
    CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk Q.target.toOver) :=
  CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.ofHom Q.projection)

omit [IsAlgClosed k] [IsMonHom i] [IsCommMonObj H.X] [Mono i] in
theorem GeometricQuotient.Construction.GeometricKernelQuotient.commutativeSheafProjection_epi : Epi Q.commutativeSheafProjection :=
  @CartierDuality.FppfEpimorphisms.Construction.Schemes.representedFppfAbMap_epi (Spec (.of k)) (Grp.mk A.scheme) (Grp.mk Q.target.toOver)
    inferInstance inferInstance (Grp.ofHom Q.projection) Q.flat Q.surjective Q.finitelyPresented

omit [IsAlgClosed k] in
theorem GeometricQuotient.Construction.GeometricKernelQuotient.commutativeSheafProjection_zero :
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.ofHom i) ≫ Q.commutativeSheafProjection = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  exact congrArg ULift.up (Quotients.FiniteDescent.Epi.Construction.subgroup_point_comp_eq_one i Q.projection Q.kernel T.unop x)

def GeometricQuotient.Construction.GeometricKernelQuotient.commutativeSheafProjection_isKernel :
    IsLimit (KernelFork.ofι (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.ofHom i)) Q.commutativeSheafProjection_zero) := by
  have : Mono (Grp.ofHom i).hom.hom := inferInstanceAs (Mono i)
  have : Mono (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.ofHom i)) := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono (Grp.ofHom i)
  refine CartierDuality.SheafKernels.Construction.Schemes.sheafKernelIsLimitOfPoints (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.ofHom i))
    Q.commutativeSheafProjection Q.commutativeSheafProjection_zero ?_
  intro T x hx
  obtain ⟨x⟩ := x
  have hx' : x ≫ Q.projection = 1 := congrArg ULift.down hx
  obtain ⟨y, hy, _⟩ := (Q.kernel T x).mp hx'
  exact ⟨ULift.up y, congrArg ULift.up hy⟩

def GeometricQuotient.Construction.GeometricKernelQuotient.commutativeSheafProjection_isCokernel :
    IsColimit (CokernelCofork.ofπ Q.commutativeSheafProjection Q.commutativeSheafProjection_zero) := by
  have : Epi Q.commutativeSheafProjection := Q.commutativeSheafProjection_epi
  exact CartierDuality.QuotientRepresentability.Construction.Exactness.cokernelOfKernelEpi _ _ _ Q.commutativeSheafProjection_isKernel

def GeometricQuotient.Construction.GeometricKernelQuotient.commutativeSheafCokernelIso :
    cokernel (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.ofHom i)) ≅
      CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk Q.target.toOver) :=
  (colimit.isColimit (parallelPair (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.ofHom i)) 0)).coconePointUniqueUpToIso
    Q.commutativeSheafProjection_isCokernel

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
