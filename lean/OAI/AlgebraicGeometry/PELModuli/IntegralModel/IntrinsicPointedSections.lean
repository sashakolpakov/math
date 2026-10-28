import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicPointedDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.Comparisons

/-! # Intrinsic Pointed Sections -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicPointedSections.PointedLiftParameters

/-! Express effective fpqc pointed-map descent directly with the ordinary
base-changed sections. No relative Hom parameter scheme is required. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

def terminalUnitIso (S : Scheme) : ⊤_ (Over S) ≅ 𝟙_ (Over S) :=
  terminalIsoIsTerminal Over.mkIdTerminal

theorem terminalUnitIso_left {S : Scheme} (T : Over S) :
    (terminal.from T ≫ (terminalUnitIso S).hom).left = T.hom := by
  exact (Category.comp_id (terminal.from T ≫ (terminalUnitIso S).hom).left).symm.trans
    (Over.w (terminal.from T ≫ (terminalUnitIso S).hom))

theorem mappedSection_pullback_fst {S T : Scheme} (u : T ⟶ S)
    {X : Over S} (x₀ : 𝟙_ (Over S) ⟶ X) :
    (Section.Comparisons.mappedSection (Over.pullback u) x₀).left ≫ pullback.fst X.hom u = u ≫ x₀.left := by
  let F := Over.pullback u
  have hm : (F.map x₀).left ≫ pullback.fst X.hom u = pullback.fst (𝟙 S) u ≫ x₀.left := by
    simp only [F, Over.pullback_map_left, pullback.lift_fst, Over.tensorUnit_hom]
  have hε : (Functor.LaxMonoidal.ε F).left ≫ pullback.fst (𝟙 S) u = u := by
    have hf : pullback.fst (𝟙 S) u = pullback.snd (𝟙 S) u ≫ u := by
      simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 S) (g := u))
    rw [hf, ← Category.assoc, Over.ε_pullback_left, IsIso.inv_hom_id, Category.id_comp]
  change ((Functor.LaxMonoidal.ε F).left ≫ (F.map x₀).left) ≫ pullback.fst X.hom u = _
  rw [Category.assoc, hm, ← Category.assoc, hε]

theorem sectionAt_nativeSource {S : Scheme} (X T : Over S)
    (x₀ : 𝟙_ (Over S) ⟶ X) :
    (PointedLift.PointedLiftParameters.sectionAt X ((terminalUnitIso S).hom ≫ x₀) T).left ≫
      (IntrinsicPointedDescent.PointedLiftParameters.nativeSourceSchemeIso X T).hom = (Section.Comparisons.mappedSection (Over.pullback T.hom) x₀).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, IntrinsicPointedDescent.PointedLiftParameters.nativeSourceSchemeIso_fst, mappedSection_pullback_fst,
      ← Over.comp_left, PointedLift.PointedLiftParameters.sectionAt, prod.lift_snd, ← Category.assoc,
      Over.comp_left, terminalUnitIso_left]
  · rw [Category.assoc, IntrinsicPointedDescent.PointedLiftParameters.nativeSourceSchemeIso_snd, ← Over.comp_left,
      PointedLift.PointedLiftParameters.sectionAt, prod.lift_fst]
    exact (Section.Comparisons.mappedSection (Over.pullback T.hom) x₀).w.symm

theorem native_pointed_equation {S : Scheme} (X Y T : Over S)
    (x₀ : 𝟙_ (Over S) ⟶ X) (y₀ : 𝟙_ (Over S) ⟶ Y)
    (h : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj Y)
    (hp : Section.Comparisons.mappedSection (Over.pullback T.hom) x₀ ≫ h = Section.Comparisons.mappedSection (Over.pullback T.hom) y₀) :
    PointedLift.PointedLiftParameters.sectionAt X ((terminalUnitIso S).hom ≫ x₀) T ≫ IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv X Y T h =
      terminal.from T ≫ ((terminalUnitIso S).hom ≫ y₀) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv_left, ← Category.assoc, sectionAt_nativeSource,
    ← Category.assoc, ← Over.comp_left, hp, mappedSection_pullback_fst]
  rw [← Category.assoc, Over.comp_left, terminalUnitIso_left]

/-- The input is the actual scalar-extended map and its usual section
equation; the output recovers that very map by native scalar extension. -/
theorem native_unit_fpqc_pointed_lift_descends
    {S : Scheme} (X Y Z : Over S) (q : Y ⟶ Z) (b : X ⟶ Z)
    (x₀ : 𝟙_ (Over S) ⟶ X) (y₀ : 𝟙_ (Over S) ⟶ Y)
    [GeometricallyConnected X.hom] [FormallyUnramified q.left]
    [LocallyOfFiniteType q.left] [IsSeparated q.left]
    (T : Over S) [Flat T.hom] [Surjective T.hom] [QuasiCompact T.hom]
    (h : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj Y)
    (hq : h ≫ (Over.pullback T.hom).map q = (Over.pullback T.hom).map b)
    (hp : Section.Comparisons.mappedSection (Over.pullback T.hom) x₀ ≫ h = Section.Comparisons.mappedSection (Over.pullback T.hom) y₀) :
    ∃! r : X ⟶ Y, r ≫ q = b ∧ x₀ ≫ r = y₀ ∧ (Over.pullback T.hom).map r = h := by
  let e := terminalUnitIso S
  obtain ⟨r, hr, huniq⟩ := IntrinsicPointedDescent.PointedLiftParameters.native_fpqc_pointed_lift_descends X Y Z q b
    (e.hom ≫ x₀) (e.hom ≫ y₀) T h hq (native_pointed_equation X Y T x₀ y₀ h hp)
  have hr₀ : x₀ ≫ r = y₀ := (cancel_epi e.hom).mp (by
    simpa only [Category.assoc] using hr.2.1)
  refine ⟨r, ⟨hr.1, hr₀, hr.2.2⟩, ?_⟩
  intro a ha
  apply huniq a
  exact ⟨ha.1, by rw [Category.assoc, ha.2.1], ha.2.2⟩

end AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicPointedSections.PointedLiftParameters

namespace AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicPointedSections

/-! Effective descent with specified source and target identifications.
The descended morphism recovers the original pointed complex morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem pointed_map_descends_through_unramified_comparison
    {S T : Scheme} (u : T ⟶ S) [Flat u] [Surjective u] [QuasiCompact u]
    (X Y Z : Over S) [GeometricallyConnected X.hom] [GrpObj Y]
    (q : Y ⟶ Z) [FormallyUnramified q.left] [LocallyOfFiniteType q.left]
    [IsSeparated q.left] (b : X ⟶ Z) (x₀ : 𝟙_ (Over S) ⟶ X)
    (W A : Over T) [GrpObj A] (w₀ : 𝟙_ (Over T) ⟶ W)
    (eX : (Over.pullback u).obj X ≅ W)
    (eY : (Over.pullback u).obj Y ≅ A) [IsMonHom eY.hom]
    (a : W ⟶ A) (f : A ⟶ (Over.pullback u).obj Z)
    (hpoint : w₀ ≫ a = 1)
    (hsource : Section.Comparisons.mappedSection (Over.pullback u) x₀ ≫ eX.hom = w₀)
    (hq : (Over.pullback u).map q = eY.hom ≫ f)
    (hb : eX.hom ≫ a ≫ f = (Over.pullback u).map b) :
    ∃ r : X ⟶ Y, r ≫ q = b ∧ x₀ ≫ r = 1 ∧
      (Over.pullback u).map r ≫ eY.hom = eX.hom ≫ a := by
  let F := Over.pullback u
  let h : F.obj X ⟶ F.obj Y := eX.hom ≫ a ≫ eY.inv
  have hq' : h ≫ F.map q = F.map b := by
    dsimp only [h]
    rw [hq]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hb
  have hp : Section.Comparisons.mappedSection F x₀ ≫ h = Section.Comparisons.mappedSection F (1 : 𝟙_ (Over S) ⟶ Y) := by
    rw [Section.Comparisons.mappedSection_one]
    dsimp only [h]
    rw [← Category.assoc, hsource, ← Category.assoc, hpoint, MonObj.one_comp]
  let T' : Over S := Over.mk u
  have : Flat T'.hom := inferInstanceAs (Flat u)
  have : Surjective T'.hom := inferInstanceAs (Surjective u)
  have : QuasiCompact T'.hom := inferInstanceAs (QuasiCompact u)
  obtain ⟨r, hr, _⟩ := PointedLiftParameters.native_unit_fpqc_pointed_lift_descends
    X Y Z q b x₀ 1 T' h hq' hp
  refine ⟨r, hr.1, hr.2.1, ?_⟩
  have hm : (Over.pullback u).map r = h := hr.2.2
  rw [hm]
  simp only [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicPointedSections

end

end OAI
