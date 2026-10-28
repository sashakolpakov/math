import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData
import OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescentOnOver
import OAI.AlgebraicGeometry.Picard.Homomorphisms.IntrinsicModuleDescent

/-! # Kernel Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent

noncomputable section

/-! The actual second-coordinate kernel action gives ordinary native descent, before any second action is imposed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseQuotientTransport OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

omit [GrpObj X] [IsCommMonObj X] [GrpObj Y] [IsMonHom g] in
/-- Equal images under the product cover give exactly the second-coordinate quotient relation. -/
theorem relation {T : Over S} (x y : T ⟶ A ⊗ X)
    (h : x ≫ (𝟙 A ⊗ₘ g) = y ≫ (𝟙 A ⊗ₘ g)) : FiberwiseQuotientTransport.Relation (snd A X) (fst A X) g x y := by
  constructor
  · have he := congrArg (fun z => z ≫ snd A Y) h
    simpa only [Category.assoc, tensorHom_snd] using he
  · have he := congrArg (fun z => z ≫ fst A Y) h
    simpa only [Category.assoc, tensorHom_fst, Category.comp_id] using he

/-- The actual kernel-difference transports form descent data for the one-coordinate cover. -/
def overDatum : (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => 𝟙 A ⊗ₘ g) where
  obj _ := L.sheaf
  hom _T _q _i _j x y hx hy :=
    FiberwiseQuotientTransport.transport (snd A X) (fst A X) g Biextension.AxisData.replaceSecond Biextension.AxisData.replaceSecond_group Biextension.AxisData.replaceSecond_base L Dv Kv
      x y (relation g x y (hx.trans hy.symm))
  hom_self _T _q _i x hx :=
    FiberwiseQuotientTransport.transport_self (snd A X) (fst A X) g Biextension.AxisData.replaceSecond Biextension.AxisData.replaceSecond_group Biextension.AxisData.replaceSecond_base L Dv Kv
      x (relation g x x (hx.trans hx.symm))
  hom_comp _T _q _i _j _k x y z hx hy hz :=
    FiberwiseQuotientTransport.transport_comp (snd A X) (fst A X) g Biextension.AxisData.replaceSecond Biextension.AxisData.replaceSecond_group Biextension.AxisData.replaceSecond_base L Dv Kv
      x y z (relation g x y (hx.trans hy.symm)) (relation g y z (hy.trans hz.symm))
      (relation g x z (hx.trans hz.symm))
  pullHom_hom _T' _T t _q _q' _hq _i _j x y hx hy x' y' htx hty :=
    FiberwiseQuotientTransport.transport_pullback (snd A X) (fst A X) g Biextension.AxisData.replaceSecond Biextension.AxisData.replaceSecond_group Biextension.AxisData.replaceSecond_base L Dv Kv
      t x y (relation g x y (hx.trans hy.symm)) x' y' _ htx hty

/-- Forgetting the fixed base retains the actual line and all its descent maps. -/
def ordinaryDatum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => (𝟙 A ⊗ₘ g).left) :=
  UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => 𝟙 A ⊗ₘ g)
    (overDatum g L Dv Kv)

/-- Native character descent can read this actual geometric one-coordinate descent datum. -/
def nativeDatum : Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent (𝟙 A ⊗ₘ g).left :=
  Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor _ (ordinaryDatum g L Dv Kv)

theorem nativeDatum_module : (nativeDatum g L Dv Kv).module = L.sheaf := rfl

/-- Evaluation on an original test scheme retains exactly its constructed quotient transport. -/
theorem nativeDatum_hom {T : Over S} (q : T ⟶ A ⊗ Y) (x y : T ⟶ A ⊗ X)
    (hx : x ≫ (𝟙 A ⊗ₘ g) = q) (hy : y ≫ (𝟙 A ⊗ₘ g) = q) :
    (nativeDatum g L Dv Kv).hom q.left x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    FiberwiseQuotientTransport.transport (snd A X) (fst A X) g Biextension.AxisData.replaceSecond Biextension.AxisData.replaceSecond_group Biextension.AxisData.replaceSecond_base L Dv Kv
      x y (relation g x y (hx.trans hy.symm)) :=
  UnderlyingDescentOnOver.hom_eq (𝟙 A ⊗ₘ g) Geometric.KernelLinearization.modulePullbacks (overDatum g L Dv Kv) q x y hx hy

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent
