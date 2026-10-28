import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar

/-! # Framed Hom -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

noncomputable section

/-! Coordinates of morphisms between trivialized line bundles and their
compatibility with arbitrary scheme pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar

variable {X Y : Scheme.{u}} {M N : X.Modules}
variable (eM : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) (eN : N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)

def framedHom (r : Γ(X, ⊤)) : M ⟶ N :=
  eM.hom ≫ ModuleScalar.scalarEnd (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) r ≫ eN.inv

def framedCoefficient (q : M ⟶ N) : Γ(X, ⊤) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction.structureSheafEndRingEquiv X (eM.inv ≫ q ≫ eN.hom)

theorem framedHom_coefficient (q : M ⟶ N) : framedHom eM eN (framedCoefficient eM eN q) = q := by
  unfold framedHom framedCoefficient
  rw [ModuleScalar.scalarEnd_structure]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

theorem framedCoefficient_hom (r : Γ(X, ⊤)) : framedCoefficient eM eN (framedHom eM eN r) = r := by
  unfold framedCoefficient framedHom
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change X.presheaf.map (𝟙 (.op ⊤)) r * 1 = r
  simp

def framedHomEquiv : Γ(X, ⊤) ≃ (M ⟶ N) where
  toFun := framedHom eM eN
  invFun := framedCoefficient eM eN
  left_inv := framedCoefficient_hom eM eN
  right_inv := framedHom_coefficient eM eN

theorem framedCoefficient_congr {M' N' : X.Modules}
    (a : M' ≅ M) (b : N' ≅ N) (q : M' ⟶ N') :
    framedCoefficient (a ≪≫ eM) (b ≪≫ eN) q =
      framedCoefficient eM eN (a.inv ≫ q ≫ b.hom) := by
  simp only [framedCoefficient, Iso.trans_inv, Iso.trans_hom, Category.assoc]

def pullbackFrame (f : Y ⟶ X) (eM : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) :
    (Scheme.Modules.pullback f).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y :=
  (Scheme.Modules.pullback f).mapIso eM ≪≫ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso f

theorem framedHom_pullback (f : Y ⟶ X) (r : Γ(X, ⊤)) :
    (Scheme.Modules.pullback f).map (framedHom eM eN r) =
      framedHom (pullbackFrame f eM) (pullbackFrame f eN) (f.appTop r) := by
  let L := Scheme.Modules.pullback f
  let v := ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso f
  change L.map (eM.hom ≫ ModuleScalar.scalarEnd (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) r ≫ eN.inv) =
    (L.map eM.hom ≫ v.hom) ≫ ModuleScalar.scalarEnd (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) (f.appTop r) ≫
      (v.inv ≫ L.map eN.inv)
  rw [L.map_comp, L.map_comp, ModuleScalar.scalarEnd_pullback]
  have hn := congrArg (fun q ↦ q ≫ v.inv) (ModuleScalar.scalarEnd_naturality v.hom (f.appTop r))
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hn
  simpa only [Category.assoc] using
    congrArg (fun q ↦ L.map eM.hom ≫ q ≫ L.map eN.inv) hn

/-- The coefficient of the actual pulled-back module map is the
pullback of its original regular-function coefficient. -/
theorem framedCoefficient_pullback (f : Y ⟶ X) (q : M ⟶ N) :
    framedCoefficient (pullbackFrame f eM) (pullbackFrame f eN)
        ((Scheme.Modules.pullback f).map q) = f.appTop (framedCoefficient eM eN q) := by
  apply (framedHomEquiv (pullbackFrame f eM) (pullbackFrame f eN)).injective
  change framedHom (pullbackFrame f eM) (pullbackFrame f eN)
    (framedCoefficient (pullbackFrame f eM) (pullbackFrame f eN)
      ((Scheme.Modules.pullback f).map q)) =
    framedHom (pullbackFrame f eM) (pullbackFrame f eN) (f.appTop (framedCoefficient eM eN q))
  rw [framedHom_coefficient, ← framedHom_pullback, framedHom_coefficient]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom
