import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.QuasiProjectiveChowCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ImmersionFiniteCoefficientDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.CompositionMorphism
import OAI.ArithmeticGeometry.Descent.CMVariety.CoefficientObjectBaseChange
import OAI.ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts

/-! # Finite Coefficient Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiniteCoefficientDescent

noncomputable section

/-! Properness of a finite-type Noetherian model descends to finitely
many coefficients. The finite Chow cover remains auxiliary: properness
is proved for the original model, including its nilpotent structure. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem closedImmersion_finiteCoefficientMap_mono
    (C B : Type) [CommRing C] [CommRing B] [Algebra C B]
    {X Y : Over (Spec (.of C))} (a : X ⟶ Y)
    {s t : Finset B} (h : s ⊆ t)
    (hs : IsClosedImmersion
      ((Over.pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C B s)).map a).left) :
    IsClosedImmersion
      ((Over.pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C B t)).map a).left := by
  let b := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C B s
  let q := ArithmeticGeometry.Descent.CMVariety.CoefficientObjectBaseChange.Abelian.objectCoefficientMap C B h
  let e := Over.pullbackComp q b
  have : IsClosedImmersion ((Over.pullback b).map a).left := hs
  have hq : q ≫ b = ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C B t := by
    dsimp only [q, b, ArithmeticGeometry.Descent.CMVariety.CoefficientObjectBaseChange.Abelian.objectCoefficientMap, ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap]
    rw [← Spec.map_comp]
    congr 1
  have : IsClosedImmersion
      ((Over.pullback q).map ((Over.pullback b).map a)).left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) q _ inferInstance
  have : IsIso (e.hom.app X).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (e.hom.app X)))
  have : IsIso (e.inv.app Y).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (e.inv.app Y)))
  rw [← hq, ← Pullback.CompositionMorphism.overPullbackCompositionMorphism_map q b a]
  change IsClosedImmersion
    ((e.hom.app X).left ≫
      ((Over.pullback q).map ((Over.pullback b).map a)).left ≫ (e.inv.app Y).left)
  infer_instance

theorem proper_eventually_of_separated_noetherian_model
    (C B : Type) [CommRing C] [IsNoetherianRing C] [CommRing B] [Algebra C B]
    (M : Over (Spec (.of C)))
    [IsNoetherian M.left] [IsSeparated M.hom] [LocallyOfFiniteType M.hom]
    [IsProper ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap C B)))).obj M).hom] :
    ∃ s : Finset B,
      IsProper ((Over.pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C B s)).obj M).hom := by
  classical
  let D := Noetherian.QuasiProjectiveChowCover.NoetherianQuasiProjectiveChowCover.build M.hom
  have : Finite D.index := D.finite
  let : Fintype D.index := Fintype.ofFinite D.index
  let Z (i : D.index) : Over (Spec (.of C)) := Over.mk (D.projection i ≫ M.hom)
  let q (i : D.index) : Z i ⟶ M := Over.homMk (D.projection i) rfl
  let j (i : D.index) : Z i ⟶ D.ambient i :=
    Over.homMk (D.embedding i) (D.embedding_base i)
  let b := Spec.map (CommRingCat.ofHom (algebraMap C B))
  let F := Over.pullback b
  have hstage (i : D.index) :
      ∃ s : Finset B,
        IsClosedImmersion
          ((Over.pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C B s)).map (j i)).left := by
    have : IsProper (D.ambient i).hom := (D.projective i).proper
    have : IsNoetherian (D.ambient i).left :=
      HilbertConstruction.Finite.TypeParameterNoetherian.finiteType_noetherian_source (D.ambient i).hom
    have : IsImmersion (j i).left := D.immersion i
    have : QuasiCompact (j i).left := D.quasiCompact i
    have : IsProper (F.map (q i)).left :=
      MorphismProperty.overPullbackMap (P := @IsProper) b (q i) (D.proper i)
    have hZB : IsProper (F.obj (Z i)).hom := by
      rw [← (F.map (q i)).w]
      infer_instance
    have : IsProper (F.obj (D.ambient i)).hom :=
      inferInstanceAs (IsProper (pullback.snd (D.ambient i).hom b))
    have : IsProper ((F.map (j i)).left ≫ (F.obj (D.ambient i)).hom) := by
      rw [(F.map (j i)).w]
      exact hZB
    have : IsProper (F.map (j i)).left :=
      IsProper.of_comp (F.map (j i)).left (F.obj (D.ambient i)).hom
    have : IsImmersion (F.map (j i)).left :=
      MorphismProperty.overPullbackMap (P := @IsImmersion) b (j i) (D.immersion i)
    have : IsClosedImmersion (F.map (j i)).left :=
      IsClosedImmersion.of_isPreimmersion (F.map (j i)).left
        (((F.map (j i)).left).isClosedMap.isClosed_range)
    exact ImmersionFiniteCoefficientDescent.closedImmersion_eventually_of_immersion C B (j i)
  choose s hs using hstage
  let t : Finset B := Finset.univ.biUnion s
  have hst (i : D.index) : s i ⊆ t := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  let bt := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C B t
  let G := Over.pullback bt
  have hZt (i : D.index) : IsProper (G.obj (Z i)).hom := by
    have : IsClosedImmersion (G.map (j i)).left :=
      closedImmersion_finiteCoefficientMap_mono C B (j i) (hst i) (hs i)
    have : IsProper (D.ambient i).hom := (D.projective i).proper
    have : IsProper (G.obj (D.ambient i)).hom :=
      inferInstanceAs (IsProper (pullback.snd (D.ambient i).hom bt))
    rw [← (G.map (j i)).w]
    infer_instance
  let q₀ : ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigma Z ⟶ M := ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigmaDesc q
  have hq₀ : Surjective q₀.left := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, z, hz⟩ := D.covers x
    exact Set.mem_iUnion.mpr ⟨i, z, hz⟩
  let e := ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigmaBaseChangeIso bt Z
  let p : ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigma (fun i => G.obj (Z i)) ⟶ G.obj M :=
    e.inv ≫ G.map q₀
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have : Surjective (G.map q₀).left :=
    MorphismProperty.overPullbackMap (P := @Surjective) bt q₀ hq₀
  have : Surjective p.left := by
    change Surjective (e.inv.left ≫ (G.map q₀).left)
    infer_instance
  have : IsProper (p.left ≫ (G.obj M).hom) := by
    rw [p.w]
    exact ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.proper_finite_sigma_desc
      (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra C B t) (fun i => (G.obj (Z i)).hom) hZt
  have : UniversallyClosed (G.obj M).hom :=
    UniversallyClosed.of_comp_surjective p.left (G.obj M).hom
  have : IsSeparated (G.obj M).hom :=
    inferInstanceAs (IsSeparated (pullback.snd M.hom bt))
  have : LocallyOfFiniteType (G.obj M).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd M.hom bt))
  exact ⟨t, ⟨⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiniteCoefficientDescent
