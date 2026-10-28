import OAI.RepresentationTheory.Theta.Geometric.FramedUnitRestriction

/-! # Framed Regular Map Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FramedRegularMapGluing

noncomputable section

/-! Compatible regular coefficients, including zeros, glue to an
actual module-sheaf morphism in the prescribed algebraic frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.RepresentationTheory.Theta.Geometric.FramedUnitRestriction

universe u

def framedRegularMap {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (g : N.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U)) : M.over U ⟶ N.over U :=
  e.hom ≫ SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r ≫ g.inv

theorem framedRegularMap_eq_of_transitions {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e₀ e₁ : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (g₀ g₁ : N.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (a b r s : Γ(X, U))
    (he : e₀.hom = e₁.hom ≫ SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U a)
    (hg : g₀.hom = g₁.hom ≫ SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U b)
    (hr : a * r = s * b) :
    framedRegularMap M N U e₀ g₀ r = framedRegularMap M N U e₁ g₁ s := by
  apply (cancel_mono g₀.hom).mp
  change (e₀.hom ≫ SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r ≫ g₀.inv) ≫ g₀.hom =
    (e₁.hom ≫ SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s ≫ g₁.inv) ≫ g₀.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hg, Iso.inv_hom_id_assoc, he]
  simp only [Category.assoc, RepresentationTheory.Theta.Geometric.FramedUnitIsomorphisms.overScalar_comp, hr]

theorem framedRegularMap_restrict {X : Scheme.{u}} (M N : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (g : N.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) (r : Γ(X, U)) :
    SheafCohomology.Projective.LinearHom.linearHomRestrict X.ringCatSheaf M N (homOfLE h).op (framedRegularMap M N U e g r) =
      framedRegularMap M N V
        (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e (Over.mk (homOfLE h)))
        (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N U g (Over.mk (homOfLE h)))
        (X.presheaf.map (homOfLE h).op r) := by
  have hg := congrArg Iso.hom ((RepresentationTheory.Theta.Geometric.FramedUnitRestriction.overIsoRestrict_symm (M := N) (N := SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) h g).trans
    (congrArg Iso.symm (RepresentationTheory.Theta.Geometric.FramedUnitRestriction.overIsoRestrict_frame h g)))
  change SheafCohomology.Projective.LinearHom.linearHomRestrict X.ringCatSheaf (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) N (homOfLE h).op g.inv =
    (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N U g (Over.mk (homOfLE h))).inv at hg
  have h₁ := SheafCohomology.Projective.OverGeneratorRestriction.linearHomRestrict_comp M (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) N h e.hom
    (SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r ≫ g.inv)
  have h₂ := SheafCohomology.Projective.OverGeneratorRestriction.linearHomRestrict_comp (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) N h
    (SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) g.inv
  exact h₁.trans (congrArg₂ (· ≫ ·) (SheafCohomology.Projective.FramedLocalHom.linearHomRestrict_frame M h e)
    (h₂.trans (congrArg₂ (· ≫ ·) (RepresentationTheory.Theta.Geometric.FramedUnitRestriction.overScalar_restrict h r) hg)))

theorem exists_morphism_of_framed_regular_sections {X : Scheme.{u}} (M N : X.Modules)
    {I : Type u} (U : I → X.Opens) (hU : iSup U = ⊤)
    (e : ∀ i, M.over (U i) ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (g : ∀ i, N.over (U i) ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (r : ∀ i, Γ(X, U i)) (a b : ∀ i j, Γ(X, U i ⊓ U j))
    (he : ∀ i j,
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (U i) (e i)
        (Over.mk (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)))).hom =
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (U j) (e j)
        (Over.mk (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)))).hom ≫
        SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf (U i ⊓ U j) (a i j))
    (hg : ∀ i j,
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N (U i) (g i)
        (Over.mk (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)))).hom =
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N (U j) (g j)
        (Over.mk (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)))).hom ≫
        SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf (U i ⊓ U j) (b i j))
    (hr : ∀ i j,
      a i j * X.presheaf.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (r i) =
        X.presheaf.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (r j) * b i j) :
    ∃ f : M ⟶ N, ∀ i, f.over (U i) = framedRegularMap M N (U i) (e i) (g i) (r i) := by
  apply SheafCohomology.Projective.ModuleHomOverlapGluing.exists_moduleHom_of_overlap_localMaps M N U hU (fun i j => U i ⊓ U j)
    (fun _ _ => inf_le_left) (fun _ _ => inf_le_right) (fun _ _ => le_rfl)
    (fun i => framedRegularMap M N (U i) (e i) (g i) (r i))
  intro i j
  rw [framedRegularMap_restrict, framedRegularMap_restrict]
  exact framedRegularMap_eq_of_transitions M N (U i ⊓ U j) _ _ _ _
    (a i j) (b i j) _ _ (he i j) (hg i j) (hr i j)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FramedRegularMapGluing
