import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ModeledQuotient
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.KernelIsoTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeCoherence

/-! # Identity Modeled Quotient -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! Remove the identity base change from the source of the actual
integral quotient, transporting its complete embedded kernel explicitly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g n : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  {F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme (Over.mk (𝟙 S))} {R : F.Model}
  (Q : Intrinsic.ModeledQuotient.Lifts.NativeModeledQuotient A (Over.mk (𝟙 S)) F R n)

def Intrinsic.ModeledQuotient.Lifts.NativeModeledQuotient.identitySourceIsogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A Q.target := by
  have : IsIso A.pullbackIdIso.inv.left := (Over.forget S).map_isIso A.pullbackIdIso.inv
  exact {
    hom := A.pullbackIdIso.inv ≫ Q.isogeny.hom
    preservesGroup := inferInstance
    finite := inferInstanceAs (IsFinite (A.pullbackIdIso.inv.left ≫ Q.isogeny.hom.left))
    flat := inferInstanceAs (Flat (A.pullbackIdIso.inv.left ≫ Q.isogeny.hom.left))
    surjective := inferInstanceAs (Surjective (A.pullbackIdIso.inv.left ≫ Q.isogeny.hom.left)) }

def Intrinsic.ModeledQuotient.Lifts.NativeModeledQuotient.identitySourceInclusion
    (_Q : Intrinsic.ModeledQuotient.Lifts.NativeModeledQuotient A (Over.mk (𝟙 S)) F R n) :
    (AbelianScheme.IsogenyQuotient.Subgroup.Construction.subgroupGroupScheme F R).X ⟶ A.scheme :=
  AbelianScheme.IsogenyQuotient.Intrinsic.Stability.Construction.nativeSubgroupInclusion A (Over.mk (𝟙 S)) F R ≫ A.pullbackIdIso.hom

theorem Intrinsic.ModeledQuotient.Lifts.NativeModeledQuotient.identitySourceIsogeny_kernel :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel Q.identitySourceIsogeny.hom Q.identitySourceInclusion := by
  have : IsMonHom (Iso.refl Q.target.scheme).hom :=
    inferInstanceAs (IsMonHom (𝟙 Q.target.scheme))
  have h := Kernel.KernelIsoTransport.prescribedKernel_isos Q.isogeny.hom
    (AbelianScheme.IsogenyQuotient.Intrinsic.Stability.Construction.nativeSubgroupInclusion A (Over.mk (𝟙 S)) F R) Q.kernel
    A.pullbackIdIso.symm (Iso.refl Q.target.scheme)
  simpa only [Intrinsic.ModeledQuotient.Lifts.NativeModeledQuotient.identitySourceIsogeny,
    Intrinsic.ModeledQuotient.Lifts.NativeModeledQuotient.identitySourceInclusion,
    Iso.symm_hom, Iso.symm_inv, Iso.refl_hom, Category.comp_id] using h

theorem Intrinsic.ModeledQuotient.Lifts.NativeModeledQuotient.identitySourceIsogeny_kernel_bound
    (T : Over S) (x : T ⟶ A.scheme) (hx : x ≫ Q.identitySourceIsogeny.hom = 1) :
    x ^ n = 1 := by
  have : IsMonHom Q.complement := Q.complementGroup
  have hk : (x ≫ A.pullbackIdIso.inv) ≫ Q.isogeny.hom = 1 := by
    simpa only [Intrinsic.ModeledQuotient.Lifts.NativeModeledQuotient.identitySourceIsogeny, Category.assoc] using hx
  have h := congrArg (fun z => (x ≫ A.pullbackIdIso.inv) ≫ z) Q.projection_complement
  rw [← Category.assoc, hk, MonObj.one_comp, MonObj.comp_pow] at h
  have hp : (x ≫ A.pullbackIdIso.inv) ^ n = 1 :=
    (congrArg (fun z : T ⟶ (A.pullback (𝟙 S)).scheme => z ^ n)
      (Category.comp_id (x ≫ A.pullbackIdIso.inv))).symm.trans h.symm
  have hh := congrArg (fun z => z ≫ A.pullbackIdIso.hom) hp
  simpa only [MonObj.pow_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    MonObj.one_comp] using hh

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
