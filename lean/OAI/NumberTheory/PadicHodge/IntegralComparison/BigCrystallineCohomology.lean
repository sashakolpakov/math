import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

/-! # Big Crystalline Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

noncomputable section

/-!
# IntegralComparison: actual big crystalline cohomology and its pullback maps

The structure sheaf is the sheafification of the ambient-ring module
presheaf. Exact restriction commutes with sheafification and constant
sheaves. It therefore induces linear pullback maps on its Ext cohomology.
Comparison with the previously defined small-site cohomology is separate.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

def modulePresheaf : (BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ ModuleCat.{u} B where
  obj U :=
    letI := U.unop.base.toAlgebra
    ModuleCat.of B U.unop.ring
  map {U V} α :=
    letI := U.unop.base.toAlgebra
    letI := V.unop.base.toAlgebra
    ModuleCat.ofHom
    { toFun := α.unop.ringMap
      map_add' := map_add α.unop.ringMap.toRingHom
      map_smul' b x := by
        change α.unop.ringMap.toRingHom (U.unop.base b * x) = V.unop.base b * α.unop.ringMap.toRingHom x
        rw [map_mul, show α.unop.ringMap.toRingHom (U.unop.base b) = V.unop.base b from
          DFunLike.congr_fun α.unop.overBase b] }
  map_id _U := by ext; rfl
  map_comp _α _β := by ext; rfl

def largePresheaf : (BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)) :=
  modulePresheaf f ⋙ ModuleCat.uliftFunctor.{u + 1} B ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : Crystalline.ExactRestriction.Coeff (B := B) ≃+* B).toRingHom

def structureSheaf : Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f :=
  (presheafToSheaf _ _).obj (largePresheaf f)

def constantUnit : Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f :=
  (constantSheaf _ _).obj (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B)))

abbrev Cohomology (n : ℕ) :=
  Abelian.Ext.{u + 2} (constantUnit (p := p) (J := J) (δ := δ) f) (structureSheaf f) n

instance cohomology_baseModule (n : ℕ) : Module B (Cohomology (p := p) (J := J) (δ := δ) f n) :=
  Module.compHom _ (ULift.ringEquiv : Crystalline.ExactRestriction.Coeff (B := B) ≃+* B).symm.toRingHom

variable {f} {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of B)}
variable (g : X ⟶ Y) (hg : g ≫ fY = f)

def presheafTransport :
    (BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg).op ⋙ largePresheaf fY ≅ largePresheaf f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

def structureTransport :
    (Crystalline.ExactRestriction.restriction g hg).obj (structureSheaf (p := p) (J := J) (δ := δ) fY) ≅ structureSheaf f :=
  ((BigCrystallineSite.postcompose g hg).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) BigCrystallineSite.Object.topology BigCrystallineSite.Object.topology).symm.app (largePresheaf fY) ≪≫
    (presheafToSheaf BigCrystallineSite.Object.topology (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapIso (presheafTransport g hg)

def constantTransport :
    (Crystalline.ExactRestriction.restriction g hg).obj (constantUnit (p := p) (J := J) (δ := δ) fY) ≅ constantUnit f :=
  ((BigCrystallineSite.postcompose g hg).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) BigCrystallineSite.Object.topology BigCrystallineSite.Object.topology).symm.app
      ((Functor.const _).obj (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B))))

/-- Pullback on the Ext cohomology of the actual big crystalline structure sheaf. -/
def pullback (n : ℕ) : Cohomology (p := p) (J := J) (δ := δ) fY n →ₗ[Crystalline.ExactRestriction.Coeff (B := B)]
    Cohomology (p := p) (J := J) (δ := δ) f n :=
  (Etale.Frobenius.extIsoCongr (Crystalline.ExactRestriction.Coeff (B := B))
    (constantTransport g hg) (structureTransport g hg) n).toLinearMap.comp
      (Crystalline.ExactRestriction.mapExt g hg (constantUnit fY) (structureSheaf fY) n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology
