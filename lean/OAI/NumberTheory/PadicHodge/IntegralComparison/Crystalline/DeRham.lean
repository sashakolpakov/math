import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.StructureDescent
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal

/-! # De Rham -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DeRham

noncomputable section

/-!
# IntegralComparison: divided-power de Rham forms on the original crystalline site

The actual ambient divided-power rings and their restriction maps define
a complex on the big crystalline site. Its degree-zero sheaf is the
original structure sheaf used to define crystalline cohomology.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local instance objectAlgebra (U : BigCrystallineSite.Object p B J δ f) : Algebra B U.ring := U.base.toAlgebra

def ambientMap {U V : BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) : V.ring →ₐ[B] U.ring :=
  { α.ringMap.toRingHom with commutes' := DFunLike.congr_fun α.overBase }

theorem ambientMap_isDPMorphism {U V : BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) :
    DividedPowers.IsDPMorphism V.dividedPowers U.dividedPowers
      (CommAlgCat.ofHom (ambientMap f α)).hom.toRingHom := α.ringMap.isDPMorphism

def formsPresheaf (n : ℕ) : (BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ ModuleCat.{u} B where
  obj U := ModuleCat.of B (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form B U.unop.ring U.unop.ideal U.unop.dividedPowers n)
  map α := ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap
    (CommAlgCat.ofHom (ambientMap f α.unop)) (ambientMap_isDPMorphism f α.unop) n)
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_id (A := CommAlgCat.of B U.unop.ring)
      (δI := U.unop.dividedPowers) (DividedPowers.DPMorphism.id U.unop.dividedPowers).isDPMorphism n ω
  map_comp α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_comp
      (CommAlgCat.ofHom (ambientMap f α.unop)) (CommAlgCat.ofHom (ambientMap f β.unop))
      (ambientMap_isDPMorphism f α.unop) (ambientMap_isDPMorphism f β.unop)
      (ambientMap_isDPMorphism f (α ≫ β).unop) n ω

def differential (n : ℕ) : formsPresheaf (p := p) (J := J) (δ := δ) f n ⟶ formsPresheaf (p := p) (J := J) (δ := δ) f (n + 1) where
  app U := ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential B U.unop.ring U.unop.ideal U.unop.dividedPowers n)
  naturality _ _ α := ModuleCat.hom_ext (LinearMap.ext (fun ω =>
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_differential (CommAlgCat.ofHom (ambientMap f α.unop))
      (ambientMap_isDPMorphism f α.unop) n ω).symm))

theorem differential_square (n : ℕ) : differential (p := p) (J := J) (δ := δ) f n ≫ differential (p := p) (J := J) (δ := δ) f (n + 1) = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  exact LinearMap.ext (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential_square B U.unop.ring U.unop.ideal U.unop.dividedPowers n)

def presheafComplex : CochainComplex ((BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ ModuleCat.{u} B) ℕ :=
  CochainComplex.of (formsPresheaf (p := p) (J := J) (δ := δ) f) (differential (p := p) (J := J) (δ := δ) f) (differential_square (p := p) (J := J) (δ := δ) f)

def sheafificationFunctor :
    ((BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f :=
  (Functor.whiskeringRight _ _ _).obj
    (ModuleCat.uliftFunctor.{u + 1} B ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ExactRestriction.Coeff (B := B) ≃+* B).toRingHom) ⋙
    presheafToSheaf BigCrystallineSite.Object.topology (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))

instance sheafification_preservesZero : (sheafificationFunctor (p := p) (J := J) (δ := δ) f).PreservesZeroMorphisms := by
  dsimp [sheafificationFunctor]
  infer_instance

def sheafComplex : CochainComplex (ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f) ℕ :=
  ((sheafificationFunctor (p := p) (J := J) (δ := δ) f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (presheafComplex (p := p) (J := J) (δ := δ) f)

def degreeZeroPresheafIso : formsPresheaf (p := p) (J := J) (δ := δ) f 0 ≅ BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) f :=
  NatIso.ofComponents
    (fun U => ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.degreeZeroEquiv B U.unop.ring U.unop.ideal
      U.unop.dividedPowers).restrictScalars B).toModuleIso)
    (fun {U V} α => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      have hω := AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol_degreeZeroEquiv B U.unop.ring U.unop.ideal U.unop.dividedPowers ω
      rw [← hω]
      change AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.degreeZeroEquiv _ _ _ _
        (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (ambientMap f α.unop))
          (ambientMap_isDPMorphism f α.unop) 0 (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol _ _ _ _ _ _)) =
        α.unop.ringMap (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.degreeZeroEquiv _ _ _ _ (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol _ _ _ _ _ _))
      rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol, AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.degreeZeroEquiv_symbol,
        AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.degreeZeroEquiv_symbol]
      rfl)

/-- Degree zero is the structure sheaf in the existing crystalline cohomology definition. -/
def degreeZeroSheafIso : (sheafComplex (p := p) (J := J) (δ := δ) f).X 0 ≅ BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f :=
  (sheafificationFunctor (p := p) (J := J) (δ := δ) f).mapIso (degreeZeroPresheafIso (p := p) (J := J) (δ := δ) f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DeRham
