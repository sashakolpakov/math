import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantGroupPoints
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Kernel

/-! # Etale Open -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleOpen.Construction

noncomputable section

/-! The kernel of a map to a constant group is an open subscheme,
by pulling back the actual identity component of that constant scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.Kernel.Construction OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantGroupPoints.CM

universe u
variable (S : Scheme.{u}) (D : Type u) [Group D]

theorem etaleGroup_unit_left :
    η[(EtaleSubgroups.Construction.etaleGroupScheme S D).X].left = Sigma.ι (fun _ : D => S) 1 := by
  change (1 : Over.mk (𝟙 S) ⟶ (EtaleSubgroups.Construction.etaleGroupScheme S D).X).left = _
  exact congrArg Over.Hom.left
    (((HodgeConjecture.HeckeCycles.ConstantGroupPoints.CM.labelsToPoints S D).map_one).symm.trans (HodgeConjecture.HeckeCycles.ConstantGroupPoints.CM.labelsToPoints_apply S D 1))

theorem etaleGroup_unit_open : IsOpenImmersion η[(EtaleSubgroups.Construction.etaleGroupScheme S D).X].left := by
  rw [etaleGroup_unit_left]
  exact (sigmaOpenCover (fun _ : D => S)).map_prop (1 : D)

variable {A : Over S} (f : A ⟶ (EtaleSubgroups.Construction.etaleGroupScheme S D).X)

theorem kernelToEtale_inclusion_open : IsOpenImmersion (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f).left := by
  have hi : IsOpenImmersion η[(EtaleSubgroups.Construction.etaleGroupScheme S D).X].left := etaleGroup_unit_open S D
  have hp := (Picard.Homomorphisms.Kernel.Construction.kernelScheme_isPullback f).map (Over.forget S)
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hp.flip hi

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleOpen.Construction
