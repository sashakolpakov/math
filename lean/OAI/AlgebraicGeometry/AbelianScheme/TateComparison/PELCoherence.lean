import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChangeCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # PEL Coherence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Canonical comparison of iterated PEL base changes, including the
integral action and full marking, for geometric correspondence branches. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

variable {R : Type u} [CommRing R] {g N : ℕ} {S T U : Scheme.{u}}

variable (A : PEL.PELFamilyData R g N S)

def PEL.PELFamilyData.pullbackId : PELModuli.PELFamilyIso (A.pullback (𝟙 S)) A where
  abelian := A.abelian.pullbackIdIso
  dual := A.dual.abelian.pullbackIdIso
  abelianGroup := A.abelian.pullbackIdIso_preservesGroup
  dualGroup := A.dual.abelian.pullbackIdIso_preservesGroup
  polarization := by
    change (Over.pullback (𝟙 S)).map A.polarizationMap.hom ≫
      A.dual.abelian.pullbackIdIso.hom = A.abelian.pullbackIdIso.hom ≫ A.polarizationMap.hom
    rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom]
    exact Over.pullbackId.hom.naturality A.polarizationMap.hom
  poincare := congrArg (fun z => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass z
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)) (AbelianModuli.HilbertConstruction.Moduli.Coherence.poincarePullbackOverMap_id A.dual)
  equivariant r := by
    rw [A.pullback_action_schemeMap, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom]
    exact Over.pullbackId.hom.naturality (End.endSchemeMap A.abelian.scheme (A.action r))
  marking T c := by
    apply Over.OverMorphism.ext
    exact (congrArg (fun z => ((A.marking.pullback (𝟙 S)).hom.app (.op T) c).val.left ≫ z)
      A.abelian.pullbackIdIso_hom_left).trans
        ((congrArg (fun x : A.abelian.Points ((Over.map (𝟙 S)).obj T) => x.left)
          (A.marking.pullback_basis (𝟙 S) T c)).trans (A.marking.basis_mapId_left T c))

def PEL.PELFamilyData.pullbackComp (f : T ⟶ S) (h : U ⟶ T) :
    PELModuli.PELFamilyIso ((A.pullback f).pullback h) (A.pullback (h ≫ f)) where
  abelian := (A.abelian.pullbackCompIso f h).symm
  dual := (A.dual.abelian.pullbackCompIso f h).symm
  abelianGroup := inferInstanceAs (IsMonHom (A.abelian.pullbackCompIso f h).inv)
  dualGroup := inferInstanceAs (IsMonHom (A.dual.abelian.pullbackCompIso f h).inv)
  polarization := by
    change (Over.pullback h).map ((Over.pullback f).map A.polarizationMap.hom) ≫
      (A.dual.abelian.pullbackCompIso f h).inv =
        (A.abelian.pullbackCompIso f h).inv ≫ (Over.pullback (h ≫ f)).map A.polarizationMap.hom
    rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
    exact (Over.pullbackComp h f).inv.naturality A.polarizationMap.hom
  poincare :=
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp
      ((A.dual.abelian.pullbackCompIso f h).inv ⊗ₘ (A.abelian.pullbackCompIso f h).inv).left
      (A.dual.poincarePullbackOverMap (h ≫ f)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)).symm.trans
      ((congrArg (fun a => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare))
        (AbelianModuli.HilbertConstruction.Moduli.Coherence.poincarePullbackOverMap_comp A.dual f h).symm).trans
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp ((A.dual.pullback f).poincarePullbackOverMap h).left
          (A.dual.poincarePullbackOverMap f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)))
  equivariant r := by
    have hleft := ((A.pullback f).pullback_action_schemeMap h r).trans
      (congrArg (fun z => (Over.pullback h).map z) (A.pullback_action_schemeMap f r))
    have hnat : (Over.pullback h).map ((Over.pullback f).map
        (End.endSchemeMap A.abelian.scheme (A.action r))) ≫ (A.abelian.pullbackCompIso f h).inv =
      (A.abelian.pullbackCompIso f h).inv ≫
        (Over.pullback (h ≫ f)).map (End.endSchemeMap A.abelian.scheme (A.action r)) := by
      rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
      exact (Over.pullbackComp h f).inv.naturality (End.endSchemeMap A.abelian.scheme (A.action r))
    exact (congrArg (fun z => z ≫ (A.abelian.pullbackCompIso f h).inv) hleft).trans
      (hnat.trans (congrArg (fun z => (A.abelian.pullbackCompIso f h).inv ≫ z)
        (A.pullback_action_schemeMap (h ≫ f) r).symm))
  marking V c := A.marking.pullback_comp_basis f h V c

/-- A commuting triangle gives the canonical PEL-family identification. -/
def PEL.PELFamilyData.pullbackFactor (f : U ⟶ T) (h : T ⟶ S) (x : U ⟶ S) (w : f ≫ h = x) :
    PELModuli.PELFamilyIso (A.pullback x) ((A.pullback h).pullback f) := by
  subst x
  exact (A.pullbackComp h f).symm

theorem PEL.PELFamilyData.pullbackFactor_abelian (f : U ⟶ T) (h : T ⟶ S) (x : U ⟶ S) (w : f ≫ h = x) :
    (A.pullbackFactor f h x w).abelian = BaseChangeCoherence.baseChangeFactorIso A.abelian f h x w := by
  subst x
  apply Iso.ext
  change (A.abelian.pullbackCompIso h f).hom = _
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_hom]
  change (Over.pullbackComp f h).hom.app A.abelian.scheme =
    𝟙 _ ≫ (Over.pullbackComp f h).hom.app A.abelian.scheme ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
