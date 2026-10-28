import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TargetIsoOpenLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ZariskiOpenCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Recovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseSquareIsomorphism

/-! # Iso Covering Sieve Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A prescribed family comparison to a modeled target is completed
from its complete polarized comparisons on a covering sieve. No
Noetherian condition is imposed on the source or parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S T : Scheme.{0}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}

/-- A complete comparison with a modeled target also allows an
isomorphic presentation of that target. -/
def Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_isomorphicModeledTarget
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)
    (B D : PolarizationData.PolarizedAbelianWithFullLevel g δ N T)
    (r : Moduli.Isomorphisms.LevelPreservingIso D (A.pullback f))
    (e : B.abelian.scheme ≅ D.abelian.scheme) (C : T.OpenCover)
    (a : ∀ i, Moduli.Isomorphisms.LevelPreservingIso (B.pullback (C.f i)) (D.pullback (C.f i)))
    (ha : ∀ i, (a i).abelian.hom = (Over.pullback (C.f i)).map e.hom) :
    Moduli.Isomorphisms.LevelPreservingIso B D := by
  let e' := e ≪≫ r.abelian
  let a' (i : C.I₀) := (a i).trans (r.pullback (C.f i))
  have ha' (i : C.I₀) : (a' i).abelian.hom = (Over.pullback (C.f i)).map e'.hom := by
    change (a i).abelian.hom ≫ (Over.pullback (C.f i)).map r.abelian.hom =
      (Over.pullback (C.f i)).map (e.hom ≫ r.abelian.hom)
    rw [ha i, Functor.map_comp]
    rfl
  exact (Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_modeledTarget A f B e' C a' ha').trans r.symm

theorem Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_isomorphicModeledTarget_abelian
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)
    (B D : PolarizationData.PolarizedAbelianWithFullLevel g δ N T)
    (r : Moduli.Isomorphisms.LevelPreservingIso D (A.pullback f))
    (e : B.abelian.scheme ≅ D.abelian.scheme) (C : T.OpenCover)
    (a : ∀ i, Moduli.Isomorphisms.LevelPreservingIso (B.pullback (C.f i)) (D.pullback (C.f i)))
    (ha : ∀ i, (a i).abelian.hom = (Over.pullback (C.f i)).map e.hom) :
    (Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_isomorphicModeledTarget A f B D r e C a ha).abelian = e := by
  apply Iso.ext
  change (e.hom ≫ r.abelian.hom) ≫ r.abelian.inv = e.hom
  rw [Category.assoc, r.abelian.hom_inv_id, Category.comp_id]

variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)
    (B : PolarizationData.PolarizedAbelianWithFullLevel g δ N T)
    (V : Over T) (R : Sieve V) (hR : R ∈ (Scheme.zariskiTopology.over T) V)
    (e : (B.pullback V.hom).abelian.scheme ≅ ((A.pullback f).pullback V.hom).abelian.scheme)
    (a : ∀ {U : Over T} (c : U ⟶ V), R c →
      Moduli.Isomorphisms.LevelPreservingIso (B.pullback U.hom) ((A.pullback f).pullback U.hom))
    (ha : ∀ {U : Over T} (c : U ⟶ V) (hc : R c),
      (a c hc).abelian.hom = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c e.hom)

def Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_modeledTarget :
    Moduli.Isomorphisms.LevelPreservingIso (B.pullback V.hom) ((A.pullback f).pullback V.hom) := by
  let I := Relative.ZariskiOpenCover.relativeZariskiOpenIndex V R
  let C : V.left.OpenCover := Scheme.Cover.mkOfCovers I
    (fun i => i.val.toScheme) (fun i => i.val.ι) (by
      intro x
      obtain ⟨i, hi⟩ := Relative.ZariskiOpenCover.relativeZariskiOpenIndex_covers V R hR x
      exact ⟨i, ⟨x, hi⟩, rfl⟩)
  let b := fun i : I => (Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv B (A.pullback f)
      (Relative.OpenModuleMaps.relativeOpenInclusion V i.val)).symm
    (a (Relative.OpenModuleMaps.relativeOpenInclusion V i.val) i.property)
  have hb (i : I) : (b i).abelian.hom = (Over.pullback (C.f i)).map e.hom :=
    Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv_symm_abelian_hom B (A.pullback f) (Relative.OpenModuleMaps.relativeOpenInclusion V i.val)
      (a (Relative.OpenModuleMaps.relativeOpenInclusion V i.val) i.property) e.hom
      (ha (Relative.OpenModuleMaps.relativeOpenInclusion V i.val) i.property)
  exact Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_isomorphicModeledTarget A (V.hom ≫ f)
    (B.pullback V.hom) ((A.pullback f).pullback V.hom)
    (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A f V.hom) e C b hb

theorem Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_modeledTarget_abelian :
    (Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_modeledTarget A f B V R hR e a ha).abelian = e := by
  unfold Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_modeledTarget
  apply Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_isomorphicModeledTarget_abelian

theorem Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_modeledTarget_hom :
    (Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_modeledTarget A f B V R hR e a ha).abelian.hom = e.hom :=
  congrArg Iso.hom (Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_modeledTarget_abelian A f B V R hR e a ha)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
