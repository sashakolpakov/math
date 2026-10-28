import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.UnderlyingDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineDescent

/-! # Affine Charts -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.AffineCharts

noncomputable section

/-!
# A geometric kernel linearization descends on faithfully flat affine charts
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.UnderlyingDescent

variable {Z : Scheme.{u}} {A B : Over Z} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle A.left)
  (D : Geometric.KernelLinearization.LineLinearization f L)
  {R S : CommRingCat.{u}} (r : R ⟶ S)
  (a : Spec S ⟶ A.left) (b : Spec R ⟶ B.left)
  (w : a ≫ f.left = Spec.map r ≫ b)

/-- Restrict the kernel-action descent datum to a commuting affine chart. -/
def chartDatum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => Spec.map r) :=
  (Pseudofunctor.DescentData.pullFunctor Geometric.KernelLinearization.modulePullbacks
    (f := fun (_ : PUnit.{1}) => f.left)
    (f' := fun (_ : PUnit.{1}) => Spec.map r) (p := b)
    (α := fun (_ : PUnit.{1}) => PUnit.unit) (p' := fun (_ : PUnit.{1}) => a)
    (fun _ => w)).obj (UnderlyingDescent.underlyingLineDatum f L D)

/-- The affine chart object is the genuine geometric pullback of the original line bundle. -/
theorem chartDatum_obj : (chartDatum f L D r a b w).obj PUnit.unit =
    (Scheme.Modules.pullback a).obj L.sheaf := rfl

theorem chartDatum_isLine :
    Line.Bundles.IsLine ((chartDatum f L D r a b w).obj PUnit.unit) := L.isLine.pullback a

/-- Effective affine descent constructs the line bundle on the quotient chart. -/
def descendedChartLine [IsNoetherianRing R] (hr : r.hom.FaithfullyFlat) :
    Line.Bundles.LineBundle (Spec R) :=
  Ordinary.AffineDescent.descendedLine r (chartDatum f L D r a b w)
    (chartDatum_isLine f L D r a b w) hr

/-- Its actual pullback is the restriction of the original line bundle to the covering chart. -/
def descendedChartPullbackIso [IsNoetherianRing R] (hr : r.hom.FaithfullyFlat) :
    (Scheme.Modules.pullback (Spec.map r)).obj (descendedChartLine f L D r a b w hr).sheaf ≅
      (Scheme.Modules.pullback a).obj L.sheaf :=
  Ordinary.AffineDescent.descendedLinePullbackIso r (chartDatum f L D r a b w)
    (chartDatum_isLine f L D r a b w) hr ≪≫ eqToIso (chartDatum_obj f L D r a b w)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.AffineCharts
