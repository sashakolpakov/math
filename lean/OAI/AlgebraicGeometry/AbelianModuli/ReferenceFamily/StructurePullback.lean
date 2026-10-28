import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureComplexScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechClasses

/-! # Structure Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructurePullback

noncomputable section

/-! The original scheme morphism induces pullback on the native
structure-sheaf H1 groups used by the tangent obstruction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

local instance nativeStructureH1_group (X : Scheme) :
    AddCommGroup (CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) 1) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH
    (_root_.Opens.grothendieckTopology X.toPresheafedSpace.carrier) 1).obj (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf)))

def structureAdditivePullbackHom {X Y : Scheme} (f : X ⟶ Y) :
    Dual.UnitCechClasses.ringAdditiveSheaf Y.sheaf ⟶
      (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f.base).obj (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) where
  hom := Functor.whiskerRight (Functor.whiskerRight f.c (forget₂ CommRingCat RingCat))
    (forget₂ RingCat AddCommGrpCat)

def nativeStructureH1Pullback {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : A ⟶ B) :
    SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule B.left) 1 →+ SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.left) 1 :=
  (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPushforwardCohomologyMap f.left.base (Dual.UnitCechClasses.ringAdditiveSheaf A.left.sheaf) 1).comp
    (CategoryTheory.Sheaf.H.map (structureAdditivePullbackHom f.left) 1)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructurePullback
