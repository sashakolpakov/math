import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.FieldPointDetection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups

/-! # Map Geometric Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.MapGeometricDetection.Construction

noncomputable section

/-! Equality of torsion-valued maps is detected after geometric base
change whenever the target torsion is etale. No reducedness is needed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

set_option backward.isDefEq.respectTransparency false in
theorem overHom_baseChange_eq_of_counit
    {S S' : Scheme.{u}} (s : S' ⟶ S) {X Y : Over S} (f g : X ⟶ Y)
    (h : (Over.mapPullbackAdj s).counit.app X ≫ f =
      (Over.mapPullbackAdj s).counit.app X ≫ g) :
    (Over.pullback s).map f = (Over.pullback s).map g := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have he := congrArg Over.Hom.left h
    change pullback.fst X.hom s ≫ f.left = pullback.fst X.hom s ≫ g.left at he
    simpa only [Over.pullback_map_left, pullback.lift_fst] using he
  · simp only [Over.pullback_map_left, pullback.lift_snd]

set_option backward.isDefEq.respectTransparency false in
theorem torsionHom_eq_of_geometric_baseChanges
    {S : Scheme.{u}} {X W : Over S} [GrpObj W] [IsCommMonObj W]
    (n : ℕ) [Etale (Groups.Construction.nativeTorsionScheme W n).hom]
    (f g : X ⟶ W) (hf : f ^ n = 1) (hg : g ^ n = 1)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      (Over.pullback s).map f = (Over.pullback s).map g) : f = g := by
  let a := Groups.Construction.nativeTorsionLift W n f hf
  let b := Groups.Construction.nativeTorsionLift W n g hg
  have hab : a = b := by
    apply Geometric.Points.Construction.etale_ext_of_geometric_points
    intro K _ _ s x
    apply (cancel_mono (Groups.Construction.nativeTorsionInclusion W n)).mp
    rw [Category.assoc, Groups.Construction.nativeTorsionLift_inclusion,
      Category.assoc, Groups.Construction.nativeTorsionLift_inclusion]
    exact Geometric.FieldPointDetection.Construction.overHom_fieldPoint_eq_of_baseChange f g s (h K s) x
  exact (Groups.Construction.nativeTorsionLift_inclusion W n f hf).symm.trans
    ((congrArg (fun z => z ≫ Groups.Construction.nativeTorsionInclusion W n) hab).trans
      (Groups.Construction.nativeTorsionLift_inclusion W n g hg))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.MapGeometricDetection.Construction
