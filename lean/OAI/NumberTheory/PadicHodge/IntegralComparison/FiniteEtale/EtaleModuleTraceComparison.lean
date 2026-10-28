import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ModuleTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceRank

/-! # Etale Module Trace Comparison -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.EtaleModuleTraceComparison

noncomputable section

/-! The actual structure-module transfer is the original de Rham
transfer after the canonical native coefficient comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]

def coefficientIso (X : Over (Spec (CommRingCat.of R))) (n : ℕ) :
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n).presheaf ≅
      ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n).obj ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} :=
  Functor.isoWhiskerRight
    ((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).mapIso
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X n))
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

variable (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] [IsProper Y.hom] [Smooth Y.hom]

def sourceIso (n : ℕ) :
    (FormSheafDuality.source R X Y f n).presheaf ≅
      ((DeRhamSheafTrace.sourceComplex R X Y f).X n).obj ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft (TopologicalSpace.Opens.map f.left.base).op (coefficientIso R X n)

theorem comparison (n : ℕ) :
    ((SheafOfModules.toSheaf Y.left.ringCatSheaf).map
      (ModuleTrace.trace R X Y f n)).hom ≫ (coefficientIso R Y n).hom =
      (sourceIso R X Y f n).hom ≫
        Functor.whiskerRight ((DeRhamSheafTrace.trace R X Y f).f n).hom
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) := by
  apply TopCat.Sheaf.hom_ext _
    ((sheafCompose (Opens.grothendieckTopology Y.left)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X n))
    (TraceBasis.isBasis R X Y f)
  intro a
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  exact ModuleTrace.normalization R X Y f a n z

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.EtaleModuleTraceComparison
