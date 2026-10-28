import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Support Image Iso -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportImageIso.Constructions

noncomputable section

/-! A reduced support and its reduced image under an actual closed
immersion are canonically isomorphic schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsClosedImmersion f.left]
  (Z : IrreducibleCloseds X.left)

instance imageMap_closed : IsClosedImmersion (Scheme.ProperSupport.Constructions.imageMap f Z) := by
  let : IsClosedImmersion (Scheme.ProperSupport.Constructions.imageMap f Z ≫ Geometric.GenericPoint.reducedSupportι (Scheme.ProperSupport.Constructions.imageSupport f Z)) := by
    rw [Scheme.ProperSupport.Constructions.imageMap_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion (Scheme.ProperSupport.Constructions.imageMap f Z) (Geometric.GenericPoint.reducedSupportι (Scheme.ProperSupport.Constructions.imageSupport f Z))

instance imageMap_isIso : IsIso (Scheme.ProperSupport.Constructions.imageMap f Z) := by
  let : AlgebraicGeometry.Surjective (Scheme.ProperSupport.Constructions.imageMap f Z) :=
    (surjective_iff (Scheme.ProperSupport.Constructions.imageMap f Z)).mpr (Scheme.ProperSupport.Constructions.imageMap_surjective f Z)
  exact isIso_of_isClosedImmersion_of_surjective (Scheme.ProperSupport.Constructions.imageMap f Z)

instance imageOverMap_isIso : IsIso (Scheme.ProperSupport.Constructions.imageOverMap f Z) := by
  let : IsIso ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map (Scheme.ProperSupport.Constructions.imageOverMap f Z)) := imageMap_isIso f Z
  exact isIso_of_reflects_iso (Scheme.ProperSupport.Constructions.imageOverMap f Z) (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase)

def supportImageIso : Scheme.RegularSupport.Constructions.supportOver X Z ≅ Scheme.RegularSupport.Constructions.supportOver Y (Scheme.ProperSupport.Constructions.imageSupport f Z) := asIso (Scheme.ProperSupport.Constructions.imageOverMap f Z)

theorem supportImageIso_inclusion :
    (supportImageIso f Z).hom ≫ Scheme.RegularSupport.Constructions.supportToAmbient Y (Scheme.ProperSupport.Constructions.imageSupport f Z) = Scheme.RegularSupport.Constructions.supportToAmbient X Z ≫ f :=
  Scheme.ProperSupport.Constructions.imageOverMap_inclusion f Z

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportImageIso.Constructions
