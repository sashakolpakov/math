import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LiteralCechPullbackClasses
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructurePullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Inverse.ImageCechCover

/-! # Structure Cech Pullback Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureCechPullbackData

noncomputable section

/-! Named original structure-sheaf Čech data keep the native H1
identification separate from the sectionwise coefficient pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def nativeStructureCechClass (X : Scheme.{0}) {I : Type} (U : I → X.Opens) (hU : iSup U = ⊤)
    (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 1)
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 1 k = 0) :
    SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X) 1 :=
  DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 0 k hk

def structureCechPullback {X Y : Scheme.{0}} (f : X ⟶ Y) {I : Type} (U : I → Y.Opens)
    (n : ℕ) (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (Dual.UnitCechClasses.ringAdditiveSheaf Y.sheaf).obj U n) :
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj (fun i => (TopologicalSpace.Opens.map f.base).obj (U i)) n :=
  LiteralCechPullback.literalCechPullback f.base U (Dual.UnitCechClasses.ringAdditiveSheaf Y.sheaf).obj
    (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj (StructurePullback.structureAdditivePullbackHom f).hom n k

theorem structureCechPullback_closed {X Y : Scheme.{0}} (f : X ⟶ Y) {I : Type} (U : I → Y.Opens)
    (n : ℕ) (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (Dual.UnitCechClasses.ringAdditiveSheaf Y.sheaf).obj U n)
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf Y.sheaf).obj U n k = 0) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj (fun i => (TopologicalSpace.Opens.map f.base).obj (U i)) n
      (structureCechPullback f U n k) = 0 :=
  LiteralCechPullback.literalCechPullback_closed f.base U (Dual.UnitCechClasses.ringAdditiveSheaf Y.sheaf).obj
    (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj (StructurePullback.structureAdditivePullbackHom f).hom n k hk

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureCechPullbackData
