import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FppfEpimorphisms
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafKernels
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Quotient Representability -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-!
# CartierDuality: native finite locally free quotients represent the actual fppf cokernel
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace QuotientRepresentability.Construction.Exactness

/-- An epimorphism whose kernel is specified is its cokernel in an abelian category. -/
def cokernelOfKernelEpi {C : Type*} [Category* C] [Abelian C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    (h : IsLimit (KernelFork.ofι f w)) [Epi g] : IsColimit (CokernelCofork.ofπ g w) := by
  let K : ShortComplex C := ShortComplex.mk f g w
  have he : K.Exact := K.exact_of_f_is_kernel h
  exact he.gIsCokernel

end QuotientRepresentability.Construction.Exactness

variable {S : Scheme.{u}} {G H : Grp (Over S)} [IsCommMonObj G.X] [IsCommMonObj H.X]
    {i : H ⟶ G} (D : IntrinsicQuotients.Construction.Schemes.NativeFiniteLocallyFreeQuotient i)

/-- The actual represented sheaf morphism of the native quotient projection. -/
def IntrinsicQuotients.Construction.Schemes.NativeFiniteLocallyFreeQuotient.sheafProjection :
    CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G ⟶ @CommutativeSheavesAb.Construction.Schemes.representedFppfAb S D.quotient D.commutative :=
  @RepresentedMorphisms.Construction.Schemes.representedFppfAbMap S G D.quotient inferInstance D.commutative D.projection

omit [IsCommMonObj H.X] in
/-- The native quotient projection is an epimorphism of fppf sheaves. -/
theorem IntrinsicQuotients.Construction.Schemes.NativeFiniteLocallyFreeQuotient.sheafProjection_epi : Epi D.sheafProjection :=
  @FppfEpimorphisms.Construction.Schemes.representedFppfAbMap_epi S G D.quotient inferInstance D.commutative D.projection
    D.projectionFlat D.projectionSurjective D.projectionFinitelyPresented

variable [Mono (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i)]

/-- The subgroup inclusion is killed by the actual sheaf quotient projection. -/
theorem IntrinsicQuotients.Construction.Schemes.NativeFiniteLocallyFreeQuotient.sheafProjection_zero :
    RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i ≫ D.sheafProjection = 0 := by
  let : Mono i.hom.hom := RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono_underlying i
  apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨h⟩
  change ULift.up (((h ≫ i.hom.hom) ≫ D.projection.hom.hom)) =
    (ULift.up 1 : ULift.{u + 1} (T.unop ⟶ D.quotient.X))
  exact congrArg ULift.up (Quotients.FiniteDescent.Epi.Construction.subgroup_point_comp_eq_one i.hom.hom D.projection.hom.hom
    D.kernel T.unop h)

/-- The native subgroup represents the kernel of the quotient morphism
on the actual commutative fppf sheaves. -/
def IntrinsicQuotients.Construction.Schemes.NativeFiniteLocallyFreeQuotient.sheafProjection_isKernel :
    IsLimit (KernelFork.ofι (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i) D.sheafProjection_zero) := by
  apply SheafKernels.Construction.Schemes.sheafKernelIsLimitOfPoints
  intro T x hx
  obtain ⟨x⟩ := x
  have hx' : x ≫ D.projection.hom.hom = 1 := congrArg ULift.down hx
  obtain ⟨h, hh, _⟩ := (D.kernel T x).mp hx'
  exact ⟨ULift.up h, (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_apply i T h).trans (congrArg ULift.up hh)⟩

/-- The native finite locally free quotient is the actual categorical
cokernel of its subgroup inclusion in commutative fppf sheaves. -/
def IntrinsicQuotients.Construction.Schemes.NativeFiniteLocallyFreeQuotient.sheafProjection_isCokernel :
    IsColimit (CokernelCofork.ofπ D.sheafProjection D.sheafProjection_zero) := by
  let : Epi D.sheafProjection := D.sheafProjection_epi
  exact @QuotientRepresentability.Construction.Exactness.cokernelOfKernelEpi (CommutativeSheavesAb.Construction.Schemes.FppfAb S) inferInstance (SheafExactness.Construction.Schemes.fppfAbAbelian S)
    _ _ _ (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i) D.sheafProjection D.sheafProjection_zero
    D.sheafProjection_isKernel inferInstance

/-- The actual fppf sheaf cokernel is represented by the constructed
native quotient group scheme. -/
def IntrinsicQuotients.Construction.Schemes.NativeFiniteLocallyFreeQuotient.sheafCokernelIso :
    cokernel (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i) ≅ @CommutativeSheavesAb.Construction.Schemes.representedFppfAb S D.quotient D.commutative :=
  (colimit.isColimit (parallelPair (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i) 0)).coconePointUniqueUpToIso
    D.sheafProjection_isCokernel

include D in
/-- The actual represented-sheaf quotient is finite locally free representable. -/
theorem IntrinsicQuotients.Construction.Schemes.NativeFiniteLocallyFreeQuotient.sheafCokernel_finiteLocallyFree :
    SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (cokernel (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i)) :=
  ⟨D.quotient, D.commutative, D.finite, D.flat, D.finitelyPresented, ⟨D.sheafCokernelIso.symm⟩⟩

omit [IsCommMonObj G.X] [IsCommMonObj H.X] [Mono (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i)] in
/-- The actual fppf quotient of a finite locally free commutative group
by a finite locally free subgroup is finite locally free representable. -/
theorem QuotientRepresentability.Construction.Schemes.sheafQuotient_finiteLocallyFree {F : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (K : Subobject F)
    (hF : SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S F) (hK : SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (K : CommutativeSheavesAb.Construction.Schemes.FppfAb S)) :
    SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (SheafQuotients.Construction.Schemes.sheafQuotient K) := by
  obtain ⟨G, hcG, hfG, hflatG, hfpG, ⟨eG⟩⟩ := hF
  obtain ⟨H, hcH, hfH, hflatH, hfpH, ⟨eH⟩⟩ := hK
  let := hcG
  let := hfG
  let := hflatG
  let := hfpG
  let := hcH
  let := hfH
  let := hflatH
  let := hfpH
  let a : CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H ⟶ CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G := eH.hom ≫ (K.arrow ≫ eG.inv)
  let j : H ⟶ G := (RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv H G).symm a
  have hj : RepresentedMorphisms.Construction.Schemes.representedFppfAbMap j = a := (RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv H G).apply_symm_apply a
  let : Mono (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap j) := hj.symm ▸ inferInstanceAs (Mono a)
  let : IsClosedImmersion j.hom.hom.left := RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_closedImmersion j
  let Q := IntrinsicQuotients.Construction.Schemes.nativeFiniteLocallyFreeQuotient G H j
  have hQ := Q.sheafCokernel_finiteLocallyFree
  exact hQ.of_iso (cokernelIsoOfEq hj ≪≫ cokernelEpiComp eH.hom (K.arrow ≫ eG.inv) ≪≫
    cokernelCompIsIso K.arrow eG.inv)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
