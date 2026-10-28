import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationKernelSheafComparison

/-! # Sheaf Section Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafSectionComparison.Construction

noncomputable section

/-! The two native torsion models give identical sheaf sections
whenever their actual included scheme points agree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ)

set_option backward.isDefEq.respectTransparency false in
theorem torsionSheafSection_eq_of_inclusion (T : Over S)
    (z : T ⟶ (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup G n).X)
    (x : T ⟶ Groups.Construction.nativeTorsionScheme G.X n)
    (h : z ≫ TorsionQuotient.SubgroupFunctor.torsionι G.X n = x ≫ Groups.Construction.nativeTorsionInclusion G.X n) :
    (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso G n).hom.hom.app (.op T) (ULift.up z) =
      (SheafComparison.Construction.kernelTorsionSheafIso G n).hom.hom.app (.op T) (ULift.up x) := by
  have hm : Mono ((kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n)).hom.app (.op T)) := inferInstance
  apply (CommGrpCat.mono_iff_injective _).mp hm
  have hz := congrArg (fun a => a.hom.app (.op T) (ULift.up z)) (CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionSheafIso_inclusion G n)
  have hx := congrArg (fun a => a.hom.app (.op T) (ULift.up x)) (SheafComparison.Construction.kernelTorsionSheafIso_inclusion G n)
  exact hz.trans ((congrArg ULift.up h).trans hx.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafSectionComparison.Construction
