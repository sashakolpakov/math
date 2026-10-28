import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FpqcPointedLifts
import Mathlib.CategoryTheory.HomCongr

/-! # Intrinsic Pointed Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicPointedDescent.PointedLiftParameters

noncomputable section

/-! Effective pointed-lift descent with exact native scalar-extension maps.
The product coordinates are obtained from the pullback adjunction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme} (X Y Z : Over S)

def nativeSourceSchemeIso (T : Over S) :
    (T ⨯ X).left ≅ pullback X.hom T.hom :=
  Over.prodLeftIsoPullback T X ≪≫ pullbackSymmetry T.hom X.hom

@[reassoc (attr := simp)] theorem nativeSourceSchemeIso_fst (T : Over S) :
    (nativeSourceSchemeIso X T).hom ≫ pullback.fst X.hom T.hom =
      (prod.snd : T ⨯ X ⟶ X).left := by
  simp only [nativeSourceSchemeIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst, Over.prodLeftIsoPullback_hom_snd]

@[reassoc (attr := simp)] theorem nativeSourceSchemeIso_snd (T : Over S) :
    (nativeSourceSchemeIso X T).hom ≫ pullback.snd X.hom T.hom =
      (prod.fst : T ⨯ X ⟶ T).left := by
  simp only [nativeSourceSchemeIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd, Over.prodLeftIsoPullback_hom_fst]

def nativeSourceIso (T : Over S) : T ⨯ X ≅
    (Over.map T.hom).obj ((Over.pullback T.hom).obj X) :=
  Over.isoMk (nativeSourceSchemeIso X T) (by
    change (nativeSourceSchemeIso X T).hom ≫ (pullback.snd X.hom T.hom ≫ T.hom) = _
    rw [← Category.assoc, nativeSourceSchemeIso_snd]
    exact (prod.fst : T ⨯ X ⟶ T).w)

/-- Native base-changed maps are the actual parameterized scheme maps. -/
def nativeHomEquiv (T : Over S) :
    ((Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj Y) ≃ (T ⨯ X ⟶ Y) :=
  ((Over.mapPullbackAdj T.hom).homEquiv ((Over.pullback T.hom).obj X) Y).symm.trans
    ((nativeSourceIso X T).symm.homCongr (Iso.refl Y))

theorem nativeHomEquiv_left (T : Over S)
    (h : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj Y) :
    (nativeHomEquiv X Y T h).left =
      (nativeSourceSchemeIso X T).hom ≫ h.left ≫ pullback.fst Y.hom T.hom := by
  change (nativeSourceSchemeIso X T).hom ≫
    (h.left ≫ pullback.fst Y.hom T.hom) ≫ 𝟙 Y.left = _
  rw [Category.comp_id]

theorem nativeHomEquiv_map (T : Over S) (r : X ⟶ Y) :
    nativeHomEquiv X Y T ((Over.pullback T.hom).map r) = prod.snd ≫ r := by
  apply Over.OverMorphism.ext
  simp only [nativeHomEquiv_left, Over.comp_left, Over.pullback_map_left,
    pullback.lift_fst, nativeSourceSchemeIso_fst_assoc]

theorem nativeHomEquiv_postcompose (T : Over S)
    (h : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj Y) (q : Y ⟶ Z) :
    nativeHomEquiv X Z T (h ≫ (Over.pullback T.hom).map q) =
      nativeHomEquiv X Y T h ≫ q := by
  apply Over.OverMorphism.ext
  simp only [nativeHomEquiv_left, Over.comp_left, Over.pullback_map_left,
    Category.assoc, pullback.lift_fst]

/-- A specified pointed lift over an fpqc extension descends uniquely, and
its native scalar extension is exactly the given morphism. -/
theorem native_fpqc_pointed_lift_descends
    (q : Y ⟶ Z) (b : X ⟶ Z)
    (x₀ : ⊤_ (Over S) ⟶ X) (y₀ : ⊤_ (Over S) ⟶ Y)
    [GeometricallyConnected X.hom] [FormallyUnramified q.left]
    [LocallyOfFiniteType q.left] [IsSeparated q.left]
    (T : Over S) [Flat T.hom] [Surjective T.hom] [QuasiCompact T.hom]
    (h : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj Y)
    (hq : h ≫ (Over.pullback T.hom).map q = (Over.pullback T.hom).map b)
    (hp : PointedLift.PointedLiftParameters.sectionAt X x₀ T ≫ nativeHomEquiv X Y T h = terminal.from T ≫ y₀) :
    ∃! r : X ⟶ Y, r ≫ q = b ∧ x₀ ≫ r = y₀ ∧ (Over.pullback T.hom).map r = h := by
  have hf : PointedLift.PointedLiftParameters.IsPointedLift X Y Z q b x₀ y₀ (nativeHomEquiv X Y T h) := by
    refine ⟨?_, hp⟩
    rw [← nativeHomEquiv_postcompose, hq, nativeHomEquiv_map]
  obtain ⟨r, hr, huniq⟩ := FpqcPointedLifts.PointedLiftParameters.fpqc_pointed_lift_descends X Y Z q b x₀ y₀ T _ hf
  have he : (Over.pullback T.hom).map r = h := by
    apply (nativeHomEquiv X Y T).injective
    rw [nativeHomEquiv_map]
    exact hr.2.2
  refine ⟨r, ⟨hr.1, hr.2.1, he⟩, ?_⟩
  intro a ha
  apply huniq a
  refine ⟨ha.1, ha.2.1, ?_⟩
  rw [← nativeHomEquiv_map, ha.2.2]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicPointedDescent.PointedLiftParameters
