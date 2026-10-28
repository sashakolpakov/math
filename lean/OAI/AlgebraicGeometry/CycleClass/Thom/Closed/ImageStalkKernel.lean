import OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure

/-! # Image Stalk Kernel -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImageStalkKernel.Constructions

noncomputable section

/-! For a genuine closed immersion of an integral scheme, the kernel
used by the original reduced-support module is the kernel of the
actual morphism on stalks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme} [IsIntegral X] (f : X ⟶ Y) [IsClosedImmersion f]

def imageSupportIso : X ≅ Geometric.GenericPoint.reducedSupportScheme (Geometric.StratumClosure.integralImageClosure f) :=
  asIso f.toImage ≪≫ Geometric.StratumClosure.reducedImageClosureIso f

theorem imageSupportIso_inclusion :
    (imageSupportIso f).hom ≫ Geometric.GenericPoint.reducedSupportι (Geometric.StratumClosure.integralImageClosure f) = f :=
  Geometric.StratumClosure.toReducedImageClosure_inclusion f

theorem imageClosure_genericPoint : IntersectionGeometry.supportPoint (Geometric.StratumClosure.integralImageClosure f) = f (genericPoint X) := by
  have h := congrArg (fun k : X ⟶ Y => k (genericPoint X)) (imageSupportIso_inclusion f)
  change Geometric.GenericPoint.reducedSupportι (Geometric.StratumClosure.integralImageClosure f) ((imageSupportIso f).hom (genericPoint X)) = f (genericPoint X) at h
  rw [genericPoint_eq_of_isOpenImmersion, Geometric.GenericPoint.reducedSupport_genericPoint_eq] at h
  exact h

omit [IsClosedImmersion f] in
theorem image_mem (x : X) : f x ∈ (Geometric.StratumClosure.integralImageClosure f : Set Y) :=
  subset_closure (Set.mem_range_self x)

theorem kernelPrime_eq_stalkMap_kernel (x : X) :
    (StalkPrimeQuotient.Constructions.kernelPrime Y (Geometric.StratumClosure.integralImageClosure f) (f x) (image_mem f x)).asIdeal =
      RingHom.ker (f.stalkMap x).hom := by
  let p : Spec (Y.presheaf.stalk (f x)) :=
    ⟨RingHom.ker (f.stalkMap x).hom, Ideal.isPrime_bot.comap (f.stalkMap x).hom⟩
  apply StalkPrimeQuotient.Constructions.kernel_eq Y (Geometric.StratumClosure.integralImageClosure f) (f x) (image_mem f x) p
  have hs := TorAlgebra.LocalSupportSpectrum.stalkMap_square f x (f x) rfl
  have he := congrArg (fun k : Spec (X.presheaf.stalk x) ⟶ Y => k (genericPoint (Spec (X.presheaf.stalk x)))) hs
  change Y.fromSpecStalk (f x) ((Spec.map (f.stalkMap x)) (genericPoint (Spec (X.presheaf.stalk x)))) =
    f (X.fromSpecStalk x (genericPoint (Spec (X.presheaf.stalk x)))) at he
  rw [SupportStalkModule.Constructions.genericPoint_image, genericPoint_eq_bot_of_affine] at he
  exact he.trans (imageClosure_genericPoint f).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImageStalkKernel.Constructions
