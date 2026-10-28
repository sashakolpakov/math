import OAI.ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts
import OAI.ArithmeticGeometry.Models.SpreadingOut.SplitComponentsBaseChange

/-! # Split Coproducts -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SplitCoproducts.Construction

noncomputable section

/-! Geometrically connected models assemble into a split finite disjoint
union; open partitions have closed components. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem geometricallyConnected_of_geometricallyIrreducible
    {X S : Scheme.{u}} (f : X ⟶ S) [GeometricallyIrreducible f] : GeometricallyConnected f := by
  refine ⟨fun k _ y Z p q hp ↦ ?_⟩
  have : IrreducibleSpace Z := GeometricallyIrreducible.geometrically_irreducibleSpace y p q hp
  infer_instance

theorem open_partition_isClosed
    {X : Scheme.{u}} {ι : Type*} (C : ι → X.Opens)
    (hdis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : (⨆ i, C i) = ⊤) (i : ι) : IsClosed (C i : Set X) := by
  classical
  have he : (C i : Set X)ᶜ = ⋃ j : {j // j ≠ i}, (C j.val : Set X) := by
    ext x
    constructor
    · intro hx
      have hxcover : x ∈ ⨆ j, C j := by rw [hcover]; trivial
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxcover
      have hji : j ≠ i := by rintro rfl; exact hx hj
      exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
    · intro hx hxi
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact (Set.disjoint_left.mp ((Opens.coe_disjoint).mpr (hdis j.val i j.property))) hj hxi
  rw [← isOpen_compl_iff, he]
  exact isOpen_iUnion (fun j ↦ (C j.val).isOpen)

theorem open_partition_closedImmersion
    {X : Scheme.{u}} {ι : Type*} (C : ι → X.Opens)
    (hdis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : (⨆ i, C i) = ⊤) (i : ι) : IsClosedImmersion (C i).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact open_partition_isClosed C hdis hcover i

theorem overSigma_hasSplitGeometricComponents
    {S : Scheme.{u}} {ι : Type u} [Finite ι] (P : ι → Over S)
    (hP : ∀ i, GeometricallyConnected (P i).hom) : Base.Construction.HasSplitGeometricComponents (ProperCoproducts.Construction.overSigma P) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let T := fun i ↦ (P i).left
  let C := fun i ↦ (Sigma.ι T (e i)).opensRange
  refine ⟨Fintype.card ι, C, ?_, ?_, ?_⟩
  · intro i j hij
    exact disjoint_opensRange_sigmaι T (e i) (e j) (fun h ↦ hij (e.injective h))
  · change (⨆ i, (Sigma.ι T (e i)).opensRange) = ⊤
    apply top_unique
    intro x _
    obtain ⟨⟨j, y⟩, rfl⟩ := (sigmaMk T).surjective x
    apply Opens.mem_iSup.mpr
    refine ⟨e.symm j, ?_⟩
    change (sigmaMk T ⟨j, y⟩) ∈ (Sigma.ι T (e (e.symm j))).opensRange
    rw [Equiv.apply_symm_apply]
    exact ⟨y, (sigmaMk_mk T j y).symm⟩
  · intro i
    have : GeometricallyConnected (P (e i)).hom := hP (e i)
    let j := Sigma.ι T (e i)
    let k := j.isoOpensRange
    have he : k.inv ≫ (P (e i)).hom = (C i).ι ≫ (ProperCoproducts.Construction.overSigma P).hom := by
      change k.inv ≫ (P (e i)).hom = (C i).ι ≫ Sigma.desc (fun a ↦ (P a).hom)
      rw [← Sigma.ι_comp_desc (fun a ↦ (P a).hom) (e i), ← Category.assoc]
      rw [Scheme.Hom.isoOpensRange_inv_comp]
    have h : IsPullback k.inv ((C i).ι ≫ (ProperCoproducts.Construction.overSigma P).hom) (P (e i)).hom (𝟙 S) :=
      IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩
    exact MorphismProperty.of_isPullback h inferInstance

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SplitCoproducts.Construction
