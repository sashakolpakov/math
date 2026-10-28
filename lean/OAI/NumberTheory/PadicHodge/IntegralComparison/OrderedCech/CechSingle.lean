import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Total
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFlip

/-! # Cech Single -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CechSingle

noncomputable section

/-! The native Čech total of a sheaf placed in one cochain degree has
the ordinary Čech cohomology of that sheaf in the shifted degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (M : X.Modules) (c : ℕ)

abbrev single := (HomologicalComplex.single X.Modules (.up ℕ) c).obj M

abbrev bicomplex := Total.Comparison.bicomplex π U (CechSingle.single M c)

theorem off_degree (p q : ℕ) (hq : q ≠ c) :
    IsZero (((bicomplex π U M c).flip.X p).X q) :=
  (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechObjectFunctor π U p).map_isZero
    (HomologicalComplex.isZero_single_obj_X (.up ℕ) c M q hq)

def rowIso : (bicomplex π U M c).X c ≅ AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U :=
  (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).mapIso
    (HomologicalComplex.singleObjXSelf (.up ℕ) c M)

def homologyIso (n : ℕ) :
    ((bicomplex π U M c).total (.up ℕ)).homology (n + c) ≅
      (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology n :=
  (HomologicalComplex.homologyMapIso ((bicomplex π U M c).totalFlipIso (.up ℕ)) (n + c)).symm ≪≫
    Single.RowTotal.homologyIso (bicomplex π U M c).flip c (off_degree π U M c) n ≪≫
    HomologicalComplex.homologyMapIso (rowIso π U M c) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CechSingle
