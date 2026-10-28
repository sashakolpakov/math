import OAI.ArithmeticGeometry.Models.Open
import OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricDescent

/-! # Finite Open Descent -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteOpenDescent.Construction

noncomputable section

/-! A finite family of quasi-compact opens descends to a common coefficient stage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

theorem finite_compact_opens_descend
    (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    (s : Finset K) (X : Over (CoefficientSystem.Constructions.Foundations.coefficientBase R K s))
    {I : Type*} [Finite I]
    (U : I → (Descent.Constructions.Foundations.expansionCone R K s X).pt.Opens)
    (hU : ∀ i, IsCompact (U i : Set (Descent.Constructions.Foundations.expansionCone R K s X).pt)) :
    ∃ (j : Over (op s)) (V : I → ((Descent.Constructions.Foundations.expansionDiagram R K s X).obj j).Opens),
      ∀ i, (Descent.Constructions.Foundations.expansionCone R K s X).π.app j ⁻¹ᵁ V i = U i := by
  classical
  let : Fintype I := Fintype.ofFinite I
  choose j V _ hV using fun i ↦ Descent.Constructions.Foundations.compact_open_descends R K s X (U i) (hU i)
  let t : Finset K := s ∪ Finset.univ.biUnion (fun i ↦ (j i).left.unop)
  have hst : s ⊆ t := Finset.subset_union_left
  have hjt (i : I) : (j i).left.unop ⊆ t := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
  let a : Over (op s) := Over.mk (homOfLE hst).op
  let m (i : I) : a ⟶ j i := Over.homMk (homOfLE (hjt i)).op (Subsingleton.elim _ _)
  refine ⟨a, fun i ↦ (Descent.Constructions.Foundations.expansionDiagram R K s X).map (m i) ⁻¹ᵁ V i, fun i ↦ ?_⟩
  rw [← Scheme.Hom.comp_preimage, (Descent.Constructions.Foundations.expansionCone R K s X).w (m i)]
  exact hV i

theorem expansion_stage_cartesian
    (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    (s : Finset K) (X : Over (CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) (j : Over (op s)) :
    IsPullback ((Descent.Constructions.Foundations.expansionCone R K s X).π.app j)
      (pullback.fst (CoefficientSystem.Constructions.Foundations.genericBaseMap R K s) X.hom)
      (pullback.fst (CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K (leOfHom j.hom.unop)) X.hom)
      (CoefficientSystem.Constructions.Foundations.genericBaseMap R K j.left.unop) := by
  let D := CoefficientSystem.Constructions.Foundations.coefficientSchemeDiagram R K
  let c := (Over.conePost D (op s)).obj (CoefficientSystem.Constructions.Foundations.coefficientSchemeCone R K)
  exact FoundationsPullback.Constructions.pullback_over_map_isPullback X.hom (c.π.app j)

theorem scheme_preimage_injective_of_surjective
    {X Y : Scheme.{u}} (p : X ⟶ Y) [Surjective p] :
    Function.Injective (fun U : Y.Opens ↦ p ⁻¹ᵁ U) := by
  intro U V h
  ext y
  obtain ⟨x, rfl⟩ := p.surjective y
  exact Iff.of_eq (congrArg (fun W : X.Opens ↦ x ∈ W) h)

theorem split_components_of_cartesian_opens
    {W X Y Z : Scheme.{u}} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback p q f g) [Surjective g]
    (n : ℕ) (U : Fin n → W.Opens) (V : Fin n → X.Opens)
    (hpre : ∀ i, p ⁻¹ᵁ V i = U i)
    (hdis : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : (⨆ i, U i) = ⊤)
    (hconn : ∀ i, GeometricallyConnected ((U i).ι ≫ q)) :
    Base.Construction.HasSplitGeometricComponents (Over.mk f) := by
  have : Surjective p := MorphismProperty.of_isPullback h.flip inferInstance
  have hinj := scheme_preimage_injective_of_surjective p
  refine ⟨n, V, ?_, ?_, ?_⟩
  · intro i j hij
    rw [disjoint_iff]
    apply hinj
    dsimp only
    rw [Scheme.Hom.preimage_inf, hpre, hpre, (hdis i j hij).eq_bot]
    rfl
  · apply hinj
    dsimp only
    rw [Scheme.Hom.preimage_iSup]
    simp only [hpre, hcover]
    rfl
  · intro i
    let r := p.resLE (V i) (U i) (hpre i).ge
    have hr : IsPullback r (U i).ι (V i).ι p :=
      IsOpenImmersion.isPullback _ _ _ _
        (Scheme.Hom.resLE_comp_ι p (hpre i).ge).symm (by simpa using hpre i)
    have : GeometricallyConnected ((U i).ι ≫ q) := hconn i
    exact GeometricDescent.Construction.geometricallyConnected_of_surjective_cartesian (hr.paste_vert h)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteOpenDescent.Construction
