import OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedLocalHom

/-! # Module Hom Overlap Gluing -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomOverlapGluing

noncomputable section

/-! Gluing module maps checked on specified pairwise intersection opens. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
universe u v

theorem exists_moduleHom_of_overlap_localMaps {X : Scheme.{u}}
    (L M : X.Modules) {ι : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (W : ι → ι → X.Opens) (hleft : ∀ i k, W i k ≤ U i)
    (hright : ∀ i k, W i k ≤ U k) (hW : ∀ i k, U i ⊓ U k ≤ W i k)
    (f : ∀ i, L.over (U i) ⟶ M.over (U i))
    (hf : ∀ i k,
      LinearHom.linearHomRestrict X.ringCatSheaf L M (homOfLE (hleft i k)).op (f i) =
      LinearHom.linearHomRestrict X.ringCatSheaf L M (homOfLE (hright i k)).op (f k)) :
    ∃ g : L ⟶ M, ∀ i, g.over (U i) = f i := by
  apply ModuleHomGluing.exists_moduleHom_of_compatible_localMaps L M U hU f
  intro i k
  let F := (LinearHom.linearHomSheaf X.ringCatSheaf L M).obj
  let si := ModuleHomGluing.linearHomLocalSection L M (U i) (f i)
  let sk := ModuleHomGluing.linearHomLocalSection L M (U k) (f k)
  have ho : F.map (homOfLE (hleft i k)).op si =
      F.map (homOfLE (hright i k)).op sk := by
    apply Subtype.ext
    change (LinearHom.ambientLinearHom X.ringCatSheaf L M).obj.map
        (homOfLE (hleft i k)).op (LinearHom.linearHomToAmbient X.ringCatSheaf L M (U i) (f i)) =
      (LinearHom.ambientLinearHom X.ringCatSheaf L M).obj.map
        (homOfLE (hright i k)).op (LinearHom.linearHomToAmbient X.ringCatSheaf L M (U k) (f k))
    rw [LinearHom.ambientLinearHom_map_linearHomToAmbient,
      LinearHom.ambientLinearHom_map_linearHomToAmbient, hf i k]
  have hi := congrArg (F.map (homOfLE (hW i k)).op) ho
  rw [← F.map_comp_apply, ← F.map_comp_apply] at hi
  exact hi

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomOverlapGluing
