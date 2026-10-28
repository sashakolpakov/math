import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AcyclicCechBoundaryDetection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechPairRecovery
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree

/-! # Regular Boundary -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.RegularBoundary

noncomputable section

/-! A zero original structure-sheaf H2 class on a separated
scheme's affine cover has a literal regular pair primitive on that
same cover. Acyclicity is proved from the actual affine intersections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) [X.IsSeparated] {I : Type} (U : I → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))

include ha in
theorem regularTriplePrimitive_of_affine_sheafClass_zero
    (w : ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l))
    (hw : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 2 (Regular.BoundaryShuffle.regularTripleCechCochain X U w) = 0)
    (hclass : DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 1
      (Regular.BoundaryShuffle.regularTripleCechCochain X U w) hw =
        (0 : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X.carrier) 2 :
          _ ⥤ AddCommGrpCat.{0}).obj (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf))) :
    ∃ v : ∀ i j, Γ(X, U i ⊓ U j), Regular.BoundaryShuffle.RegularTripleBoundary X U v w := by
  let : (HilbertConstruction.Line.Bundles.structureModule X).IsQuasicoherent :=
    Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (HilbertConstruction.Line.Bundles.LineBundle.trivial X)
  have hH : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) :=
    SheafCohomology.Cech.Projective.affineCoverIntersectionsAcyclic (HilbertConstruction.Line.Bundles.structureModule X) U ha
  obtain ⟨c, hc⟩ := AcyclicCechBoundaryDetection.cech_boundary_of_acyclic_sheaf_class_zero U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU hH 1
    (Regular.BoundaryShuffle.regularTripleCechCochain X U w) hw hclass
  exact Regular.CechPairRecovery.regularTriplePrimitive_of_cech_boundary X U w c hc

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.RegularBoundary
