import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomOverlapGluing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible

/-! # Line Bundle Iso Gluing -/

namespace OAI.RepresentationTheory.Theta.Geometric.LineBundleIsoGluing

noncomputable section

/-! Compatible local isomorphisms of actual module sheaves glue to an
actual global isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomOverlapGluing
universe u

theorem moduleMap_isIso_of_over {X : Scheme.{u}} {M N : X.Modules}
    (g : M ⟶ N) {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, IsIso (g.over (U i))) : IsIso g := by
  apply AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isIso_of_isIso_restrict g U hU
  intro i
  let F := (Scheme.Modules.overEquiv (U i)).functor
  let a := (Scheme.Modules.overFunctorEquiv (U i)).app M
  let b := (Scheme.Modules.overFunctorEquiv (U i)).app N
  let : IsIso (g.over (U i)) := h i
  have he : (Scheme.Modules.restrictFunctor (U i).ι).map g =
      a.inv ≫ F.map (g.over (U i)) ≫ b.hom := by
    have hn := (Scheme.Modules.overFunctorEquiv (U i)).hom.naturality g
    change F.map (g.over (U i)) ≫ b.hom = a.hom ≫ _ at hn
    rw [hn]
    simp
  rw [he]
  infer_instance

theorem exists_moduleIso_of_localIsos {X : Scheme.{u}} (M N : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (e : ∀ i, M.over (U i) ≅ N.over (U i))
    (he : ∀ i k,
      AlgebraicGeometry.SheafCohomology.Projective.LinearHom.linearHomRestrict X.ringCatSheaf M N (homOfLE (show U i ⊓ U k ≤ U i from inf_le_left)).op (e i).hom =
      AlgebraicGeometry.SheafCohomology.Projective.LinearHom.linearHomRestrict X.ringCatSheaf M N (homOfLE (show U i ⊓ U k ≤ U k from inf_le_right)).op (e k).hom) :
    ∃ g : M ≅ N, ∀ i, g.hom.over (U i) = (e i).hom := by
  obtain ⟨g, hg⟩ := AlgebraicGeometry.SheafCohomology.Projective.ModuleHomOverlapGluing.exists_moduleHom_of_overlap_localMaps M N U hU
    (fun i k => U i ⊓ U k) (fun _ _ => inf_le_left) (fun _ _ => inf_le_right)
    (fun _ _ => le_rfl) (fun i => (e i).hom) he
  let : IsIso g := moduleMap_isIso_of_over g U hU (fun i => by rw [hg i]; infer_instance)
  exact ⟨asIso g, hg⟩

end

end OAI.RepresentationTheory.Theta.Geometric.LineBundleIsoGluing
