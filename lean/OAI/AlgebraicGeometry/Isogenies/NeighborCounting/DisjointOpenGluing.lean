import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenHomComparison

/-! # Disjoint Open Gluing -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DisjointOpenGluing

noncomputable section

/-! Gluing actual module isomorphisms on disjoint open components.
This assembles a covering family before effective fpqc descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenHomComparison

variable {X : Scheme.{u}} (M N : X.Modules)

theorem hom_bottom_subsingleton :
    Subsingleton ((ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomTypeSheaf M N).obj.obj (op ⊥)) := by
  constructor
  intro a b
  let F : TopCat.Sheaf (Type u) X := ⟨(ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomTypeSheaf M N).obj, (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomTypeSheaf M N).property⟩
  apply F.eq_of_locally_eq' (fun _ : Empty ↦ (⊥ : X.Opens)) ⊥
    (fun _ ↦ homOfLE le_rfl) (by simp)
  intro i
  cases i

theorem disjoint_compatible {ι : Type*} (U : ι → X.Opens)
    (hd : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (q : ∀ i, (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomTypeSheaf M N).obj.obj (op (U i))) :
    TopCat.Presheaf.IsCompatible (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomTypeSheaf M N).obj U q := by
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · have h : U i ⊓ U j = ⊥ := (hd hij).eq_bot
    have : Subsingleton ((ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomTypeSheaf M N).obj.obj (op (U i ⊓ U j))) := by
      rw [h]
      exact hom_bottom_subsingleton M N
    exact Subsingleton.elim _ _

theorem existsUnique_disjoint_hom {ι : Type*} (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U) (hd : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (q : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ⟶
      (Scheme.Modules.pullback (U i).ι).obj N) :
    ∃! a : M ⟶ N, ∀ i, (Scheme.Modules.pullback (U i).ι).map a = q i :=
  OpenHomComparison.existsUnique_hom_of_open_pullbacks M N U hU q
    (disjoint_compatible M N U hd (fun i ↦ (OpenHomComparison.openHomEquiv M N (U i)).symm (q i)))

theorem existsUnique_disjoint_iso {ι : Type*} (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U) (hd : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ≅
      (Scheme.Modules.pullback (U i).ι).obj N) :
    ∃! d : M ≅ N, ∀ i, (Scheme.Modules.pullback (U i).ι).mapIso d = e i := by
  obtain ⟨a, ha, hu⟩ := existsUnique_disjoint_hom M N U hU hd (fun i ↦ (e i).hom)
  obtain ⟨b, hb, _⟩ := existsUnique_disjoint_hom N M U hU hd (fun i ↦ (e i).inv)
  have hab : a ≫ b = 𝟙 M := by
    apply OpenHomComparison.hom_eq_of_open_pullbacks M M U hU
    intro i
    let L := Scheme.Modules.pullback (U i).ι
    exact (L.map_comp a b).trans ((congrArg₂ (fun r s ↦ r ≫ s) (ha i) (hb i)).trans
      ((e i).hom_inv_id.trans (L.map_id M).symm))
  have hba : b ≫ a = 𝟙 N := by
    apply OpenHomComparison.hom_eq_of_open_pullbacks N N U hU
    intro i
    let L := Scheme.Modules.pullback (U i).ι
    exact (L.map_comp b a).trans ((congrArg₂ (fun r s ↦ r ≫ s) (hb i) (ha i)).trans
      ((e i).inv_hom_id.trans (L.map_id N).symm))
  let d : M ≅ N := ⟨a, b, hab, hba⟩
  refine ⟨d, fun i ↦ Iso.ext (ha i), ?_⟩
  intro d' hd'
  apply Iso.ext
  exact hu d'.hom (fun i ↦ congrArg Iso.hom (hd' i))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DisjointOpenGluing
