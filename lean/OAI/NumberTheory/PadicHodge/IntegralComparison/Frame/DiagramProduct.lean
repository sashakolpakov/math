import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.DeRhamProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct

/-! # Diagram Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.DiagramProduct

noncomputable section

/-! Actual frame PD de Rham diagrams carry the native all-degree
Čech total cup and its categorical cohomology product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))
  {C : Type v} [Category.{w} C]
  (H : Cᵒᵖ ⥤ (BigCrystallineSite.Object p B J δ f)ᵒᵖ)

abbrev diagram := H ⋙ GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor f
abbrev complex := Cech.ComplexDiagramCoordinates.complex (diagram f H)

def pairing (a b : ℕ) (V : Cᵒᵖ) :=
  RelativeFrame.Product.framePairing (H.obj V).unop a b

theorem natural (a b : ℕ) {U V : Cᵒᵖ} (α : U ⟶ V)
    (x : ((complex f H).X a).obj U) (y : ((complex f H).X b).obj U) :
    ((complex f H).X (a+b)).map α (pairing f H a b U x y) =
      pairing f H a b V (((complex f H).X a).map α x) (((complex f H).X b).map α y) :=
  DeRhamProduct.natural f a b (H.map α) x y

private theorem cast (V : Cᵒᵖ) {a b : ℕ} (h : a=b)
    (x : ((complex f H).X a).obj V) :
    Presheaf.CechProduct.sectionDegreeCast (complex f H) h V x =
      Cochain.CohomologyCup.degreeCast ((diagram f H).obj V) h x := by
  subst b
  rfl

theorem differential (a b : ℕ) (V : Cᵒᵖ)
    (x : ((complex f H).X a).obj V) (y : ((complex f H).X b).obj V) :
    ((complex f H).d (a+b) (a+b+1)).app V (pairing f H a b V x y) =
      Presheaf.CechProduct.sectionDegreeCast (complex f H) (by omega) V
        (pairing f H (a+1) b V (((complex f H).d a (a+1)).app V x) y) +
      (-1 : ℤ)^a • Presheaf.CechProduct.sectionDegreeCast (complex f H) (by omega) V
        (pairing f H a (b+1) V x (((complex f H).d b (b+1)).app V y)) := by
  exact (DeRhamProduct.differential f a b (H.obj V) x y).trans
    (congrArg₂ (fun x y => x + (-1 : ℤ)^a • y)
      (cast f H V (by omega : (a+1)+b = a+b+1) _).symm
      (cast f H V (by omega : a+(b+1) = a+b+1) _).symm)

variable [HasBinaryProducts C] {ι : Type} [Finite ι] (U : ι → C)

abbrev total := Presheaf.TotalCup.CechProduct.total (NonemptyCechNerve.nerve U) (complex f H)
abbrev cup := Presheaf.TotalCup.CechProduct.totalCup (NonemptyCechNerve.nerve U) (complex f H)
  (pairing f H)
abbrev differential_cup := Presheaf.TotalLeibniz.CechProduct.differential_totalCup
  (NonemptyCechNerve.nerve U) (complex f H) (pairing f H) (natural f H) (differential f H)
abbrev cohomologyCup := Presheaf.CohomologyProduct.Cech.cohomologyCup
  (NonemptyCechNerve.nerve U) (complex f H) (pairing f H) (natural f H) (differential f H)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.DiagramProduct
