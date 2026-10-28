import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedKernelAmbientInclusion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.SubgroupComparisons
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.IsoTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedIntrinsicSubgroup

/-! # Transported Kernel Parameter Family -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedKernelParameterFamily.Family

noncomputable section

/-! The transported active kernel is the inverse image of the integral
embedded family under the actual ambient source isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedIntrinsicSubgroup.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedGenericKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedKernelAmbientInclusion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.SubgroupComparisons
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.IsoTransport
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

universe u

variable {S₁ S₂ S₀ : Scheme.{u}} (f : S₀ ⟶ S₁) (g : S₀ ⟶ S₂)
  (G A : Grp (Over S₁)) (H B : Grp (Over S₂))
  (i : G ⟶ A) (j : H ⟶ B)
  (e : (Over.pullback f).mapGrp.obj G ≅ (Over.pullback g).mapGrp.obj H)
  (a : (Over.pullback f).mapGrp.obj A ≅ (Over.pullback g).mapGrp.obj B)
  (K : Kernel.Properties.FiniteFlatKernel H.X)
  (square : e.hom ≫ (Over.pullback g).mapGrp.map j =
    (Over.pullback f).mapGrp.map i ≫ a.hom)

include square in
theorem transportedKernel_parameter_family :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback a.hom.hom.hom
      (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter B (Over.mk g)
        (Kernel.Base.fixedKernelFamily (K.inclusion ≫ j.hom.hom))) =
      Kernel.Base.fixedKernelFamily (P := Over.mk (𝟙 S₀))
        ((TransportedGenericKernel.transportedGenericKernel f g G H e K).inclusion ≫ (Over.pullback f).map i.hom.hom) := by
  let aRaw : (Over.pullback f).obj A.X ≅ (Over.pullback g).obj B.X :=
    (Grp.forget (Over S₀)).mapIso a
  have : IsMonHom aRaw.hom := a.hom.hom.isMonHom_hom
  have : IsMonHom (Iso.refl ((Over.pullback g).obj K.carrier)).hom :=
    inferInstanceAs (IsMonHom (𝟙 ((Over.pullback g).obj K.carrier)))
  let u : (Over.pullback g).obj K.carrier ⟶ (Over.pullback f).obj A.X :=
    (TransportedGenericKernel.transportedGenericKernel f g G H e K).inclusion ≫ (Over.pullback f).map i.hom.hom
  let v : (Over.pullback g).obj K.carrier ⟶ (Over.pullback g).obj B.X :=
    (Over.pullback g).map (K.inclusion ≫ j.hom.hom)
  have : IsMonHom v := inferInstanceAs (IsMonHom ((Over.pullback g).map (K.inclusion ≫ j.hom.hom)))
  let k : Grp.mk K.carrier ⟶ B := Grp.ofHom (K.inclusion ≫ j.hom.hom)
  have hv : (𝟙 ((Over.pullback g).obj K.carrier)) ≫ v = u ≫ aRaw.hom :=
    (Category.id_comp v).trans
      (((Over.pullback g).map_comp K.inclusion j.hom.hom).trans
        (TransportedKernelAmbientInclusion.transportedKernel_ambient_inclusion f g G A H B i j e a K square).symm)
  have : IsMonHom u := AbelianScheme.IsogenyQuotient.SupportedIntrinsicSubgroup.Construction.isMonHom_of_mono_factorization u aRaw.hom v
    (hv.symm.trans (Category.id_comp v))
  have hp := Parameter.SubgroupComparisons.relativeParameter_fixed_kernel (Grp.mk K.carrier) B (Over.mk g) k
  exact (congrArg (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback aRaw.hom) hp).trans
    (Kernel.IsoTransport.fixedKernelFamily_iso_square aRaw (Iso.refl ((Over.pullback g).obj K.carrier)) u v hv)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedKernelParameterFamily.Family
