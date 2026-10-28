import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramBaseChangeComposition
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Pullback Recovery Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.PullbackRecoveryIso

noncomputable section

/-! Recovery isomorphisms persist after inserting an intermediate coefficient extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem isIso_iterated_overPullback
    {C : Type u} [Category.{v} C] [HasPullbacks C] {S T U : C}
    (f : T ⟶ S) (g : U ⟶ T) (h : U ⟶ S) (hw : g ≫ f = h)
    {X Y : Over S} (q : X ⟶ Y) [IsIso ((Over.pullback h).map q)] :
    IsIso ((Over.pullback g).map ((Over.pullback f).map q)) := by
  let e : Over.pullback h ≅ Over.pullback f ⋙ Over.pullback g :=
    (eqToIso (congrArg (fun k : U ⟶ S => Over.pullback k) hw)).symm ≪≫ Over.pullbackComp g f
  exact (NatIso.isIso_map_iff e q).mp inferInstance

theorem isIso_coefficient_iterated_overPullback
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R] (D : Subalgebra C R)
    {X Y : Over (Spec (.of C))} (q : X ⟶ Y)
    [IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R)))).map q)] :
    IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D R)))).map
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D)))).map q)) := by
  apply isIso_iterated_overPullback _ _
    (Spec.map (CommRingCat.ofHom (algebraMap C R))) _ q
  rw [← Spec.map_comp]
  congr 1

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.PullbackRecoveryIso
