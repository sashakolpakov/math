import OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible

/-! # Base Structure Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseStructureSections

noncomputable section

/-! The scalar multiple of the actual constant function one in the
base-linear structure-sheaf module is the original pullback on functions. -/

universe u
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S)

def baseStructureUnitMap : Γ(S, ⊤) →ₗ[Γ(S, ⊤)] (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)).obj (op ⊤) :=
  LinearMap.toSpanSingleton Γ(S, ⊤) _ (1 : Γ(X, ⊤))

theorem baseStructureUnitMap_apply (r : Γ(S, ⊤)) :
    baseStructureUnitMap f r = f.appTop r := by
  change (X.presheaf.map (𝟙 (op (⊤ : X.Opens)))).hom (f.appTop r) * 1 = f.appTop r
  rw [CategoryTheory.Functor.map_id]
  exact mul_one _

theorem baseStructureUnitMap_bijective [IsIso f.appTop] :
    Function.Bijective (baseStructureUnitMap f) := by
  have he : (baseStructureUnitMap f : Γ(S, ⊤) → Γ(X, ⊤)) = (f.appTop : Γ(S, ⊤) → Γ(X, ⊤)) :=
    funext (baseStructureUnitMap_apply f)
  rw [he]
  exact ConcreteCategory.bijective_of_isIso f.appTop

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseStructureSections
