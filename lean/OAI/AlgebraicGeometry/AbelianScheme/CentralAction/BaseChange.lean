import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.BaseChange.Construction

noncomputable section

/-! Canonical PEL identifications for base change, retaining the action,
polarization, Poincare bundle, and every full-level label. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

universe u
variable {R : Type u} [CommRing R] {g N : ℕ} {S S' S'' : Scheme.{u}}

def pelIsoPullback {A B : TateComparison.PEL.PELFamilyData R g N S}
    (e : TateComparison.PELModuli.PELFamilyIso A B) (f : S' ⟶ S) : TateComparison.PELModuli.PELFamilyIso (A.pullback f) (B.pullback f) where
  abelian := (Over.pullback f).mapIso e.abelian
  dual := (Over.pullback f).mapIso e.dual
  abelianGroup := inferInstanceAs (IsMonHom ((Over.pullback f).map e.abelian.hom))
  dualGroup := inferInstanceAs (IsMonHom ((Over.pullback f).map e.dual.hom))
  polarization := ((Over.pullback f).map_comp A.polarizationMap.hom e.dual.hom).symm.trans
    ((congrArg (fun h => (Over.pullback f).map h) e.polarization).trans
      ((Over.pullback f).map_comp e.abelian.hom B.polarizationMap.hom))
  poincare :=
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp
      ((Over.pullback f).map e.dual.hom ⊗ₘ (Over.pullback f).map e.abelian.hom).left
      (B.dual.poincarePullbackOverMap f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)).symm.trans
        ((congrArg (fun h => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass h (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare))
          (AbelianModuli.HilbertConstruction.Moduli.BaseChange.poincarePullbackOverMap_naturality A.dual B.dual e.dual.hom e.abelian.hom f)).trans
          ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (A.dual.poincarePullbackOverMap f).left
            (e.dual.hom ⊗ₘ e.abelian.hom).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)).trans
            (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.dual.poincarePullbackOverMap f).left) e.poincare)))
  equivariant r := by
    rw [TateComparison.PEL.PELFamilyData.pullback_action_schemeMap, TateComparison.PEL.PELFamilyData.pullback_action_schemeMap]
    exact ((Over.pullback f).map_comp _ _).symm.trans
      ((congrArg (fun a => (Over.pullback f).map a) (e.equivariant r)).trans
        ((Over.pullback f).map_comp _ _))
  marking T c := by
    apply (B.abelian.baseChangePointsEquiv f T).injective
    exact (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map e.abelian.hom f T
      ((A.marking.pullback f).hom.app (.op T) c).val).trans
        ((congrArg (fun h => h ≫ e.abelian.hom) (A.marking.pullback_basis f T c)).trans
          ((e.marking ((Over.map f).obj T) c).trans (B.marking.pullback_basis f T c).symm))

def pelPullbackComp (A : TateComparison.PEL.PELFamilyData R g N S) (f : S' ⟶ S) (h : S'' ⟶ S') :
    TateComparison.PELModuli.PELFamilyIso ((A.pullback f).pullback h) (A.pullback (h ≫ f)) where
  abelian := (A.abelian.pullbackCompIso f h).symm
  dual := (A.dual.abelian.pullbackCompIso f h).symm
  abelianGroup := inferInstanceAs (IsMonHom (A.abelian.pullbackCompIso f h).inv)
  dualGroup := inferInstanceAs (IsMonHom (A.dual.abelian.pullbackCompIso f h).inv)
  polarization := by
    change (Over.pullback h).map ((Over.pullback f).map A.polarizationMap.hom) ≫
      (A.dual.abelian.pullbackCompIso f h).inv =
        (A.abelian.pullbackCompIso f h).inv ≫
          (Over.pullback (h ≫ f)).map A.polarizationMap.hom
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
    change (Over.pullback h).map ((Over.pullback f).map
      (TateComparison.End.endSchemeMap A.abelian.scheme (A.action r))) ≫
        (A.abelian.pullbackCompIso f h).inv = _
    rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
    exact (Over.pullbackComp h f).inv.naturality (TateComparison.End.endSchemeMap A.abelian.scheme (A.action r))
  marking T c := A.marking.pullback_comp_basis f h T c

def pelPullbackId (A : TateComparison.PEL.PELFamilyData R g N S) : TateComparison.PELModuli.PELFamilyIso (A.pullback (𝟙 S)) A where
  abelian := A.abelian.pullbackIdIso
  dual := A.dual.abelian.pullbackIdIso
  abelianGroup := A.abelian.pullbackIdIso_preservesGroup
  dualGroup := A.dual.abelian.pullbackIdIso_preservesGroup
  polarization := by
    change (Over.pullback (𝟙 S)).map A.polarizationMap.hom ≫
      A.dual.abelian.pullbackIdIso.hom =
        A.abelian.pullbackIdIso.hom ≫ A.polarizationMap.hom
    rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom]
    exact Over.pullbackId.hom.naturality A.polarizationMap.hom
  poincare := congrArg (fun z => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass z
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)) (AbelianModuli.HilbertConstruction.Moduli.Coherence.poincarePullbackOverMap_id A.dual)
  equivariant r := by
    rw [TateComparison.PEL.PELFamilyData.pullback_action_schemeMap, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom]
    exact Over.pullbackId.hom.naturality (TateComparison.End.endSchemeMap A.abelian.scheme (A.action r))
  marking T c := by
    apply Over.OverMorphism.ext
    exact (congrArg (fun z => ((A.marking.pullback (𝟙 S)).hom.app (.op T) c).val.left ≫ z)
      A.abelian.pullbackIdIso_hom_left).trans
        ((congrArg (fun x : A.abelian.Points ((Over.map (𝟙 S)).obj T) => x.left)
          (A.marking.pullback_basis (𝟙 S) T c)).trans (A.marking.basis_mapId_left T c))

variable {E : Type u} [Field E] [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {B : Scheme.{u}}

/-- A PEL isomorphism of classified families forces equality of the
classifying maps, with all markings and polarization data retained. -/
theorem classifying_maps_eq_of_pelIso
    (M : TateComparison.PELModuli.PELModuliCandidate P N B)
    (baseAction : NumberField.RingOfIntegers E →+* Γ(B, ⊤))
    (hclass : M.ClassifiesReduced baseAction)
    (T : Over B) [IsReduced T.left] (x y : T ⟶ M.space)
    (e : TateComparison.PELModuli.PELFamilyIso (M.family.pullback x.left) (M.family.pullback y.left)) : x = y := by
  obtain ⟨z, _, hu⟩ := hclass.2 T (M.family.pullback y.left) (hclass.1 T y)
  exact (hu x ⟨e⟩).trans (hu y ⟨TateComparison.PELModuli.PELFamilyIso.refl _⟩).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.BaseChange.Construction
